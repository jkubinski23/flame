#!/usr/bin/env python3
"""Print the memory summary (USS = Private_Clean + Private_Dirty) from /proc/<pid>/smaps, and
with -f generate a USS flame graph.

Mappings are classified the same way as in smaps_flamegraph.html (dynamic allocator,
thread stack, executable, anonymous, file backed); with -f they are written to a self-contained
interactive HTML page (zoom, search, tooltips, per-process / per-group tables).
The page has two views of the same tree: "USS", and "Referenced pages": the size of every
mapping (without ---p reservations) split into its referenced pages (present in RAM or
swapped out, from /proc/<pid>/pagemap) and its not referenced pages, in address order; the
referenced pages are split by page type: 4K page, transparent huge page, huge page (hugetlbfs),
locked (mlock), KSM, slab, zero page, swapped out (exact from /proc/kpageflags when run as root,
otherwise estimated from the smaps counters; swapped out pages are always exact).

examples:
  flame.py -p 1234           memory summary of one process
  flame.py -p 1234 -f        collect flame graph (flame_<program>_1234_<time>.html)
  flame.py -p 1234 -f -g     collect global variables (>4K) statistics for executable in the flame graph
  flame.py -p 1234 -f -g all collect global variables of all its shared libraries
  flame.py -p 1234 -m        collect mallinfo() statistics (via gdb)
  flame.py -p 1234 -t        execute malloc_trim(0) (via gdb)
  flame.py -s                memory summary for whole system
  flame.py -s -f             collect flame graph for whole system
  flame.py -i FILE           process raw smaps file
"""
import argparse
import bisect
import bz2
import gzip
import html
import json
import lzma
import os
import re
import signal
import struct
import subprocess
import sys
import time
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor

HEADER_RE = re.compile(r"^([0-9a-fA-F]+)-([0-9a-fA-F]+)\s+(\S{4})\s+([0-9a-fA-F]+)\s+(\S+)\s+(\d+)\s*(.*)$")
PROC_RE = re.compile(r"^==> /proc/(\d+)/smaps <==")
# the format of the smaps copies written by mtrace_report.py
PAGEMAP_RE = re.compile(r"^# mtrace (pagemap|referenced) 0x([0-9a-fA-F]+) 0x([0-9a-fA-F]+)$")
# page types of the referenced pages: "# mtrace pagekinds pfn|nopfn" (pfn: from /proc/kpageflags, nopfn:
# only the swapped out pages are known), then the runs of pages that are not normal 4K pages
PAGEKINDS_RE = re.compile(r"^# mtrace pagekinds (pfn|nopfn)$")
PAGEKIND_RE = re.compile(r"^# mtrace pagekind 0x([0-9a-fA-F]+) 0x([0-9a-fA-F]+) (\w+)$")
KEEP_FIELDS = {"Size", "Rss", "Pss", "Shared_Clean", "Shared_Dirty", "Private_Clean", "Private_Dirty",
               "Referenced", "Anonymous", "Swap", "AnonHugePages", "ShmemPmdMapped", "FilePmdMapped",
               "Locked", "KernelPageSize", "Private_Hugetlb", "Shared_Hugetlb"}
PAGE_KINDS = OrderedDict([
    ("4k", "4K page"), ("thp", "transparent huge page"), ("huge", "huge page (hugetlbfs)"),
    ("locked", "locked (mlock)"), ("ksm", "KSM"), ("slab", "slab"), ("zero", "zero page"),
    ("swap", "swapped out"),
])
TOOLTIP_FIELDS = ["Size", "KernelPageSize", "Rss", "Pss", "Shared_Clean", "Shared_Dirty", "Anonymous", "Swap",
                  "Private_Hugetlb", "Shared_Hugetlb"]

CATEGORIES = ["Dynamic allocator", "Thread stack", "Executable", "Anonymous", "File Backed"]
CATEGORY_KIND = {
    "Dynamic allocator": "alloc", "Thread stack": "stack", "Executable": "exec",
    "Anonymous": "anon", "File Backed": "file",
}
# index in the path where the "<program>[<PID>]" level is inserted in the grouped system view
PROC_DEPTH = {"Executable": 3, "Anonymous": 2, "File Backed": 2}
SUBGROUP_ORDER = [
    "Heap", "glibc malloc", "glibc loader malloc", "glibc malloc arena",
    "main stack", "pthread stack", "stack guard (---p)",
    "Binary", "Dynamic libraries",
    ".text (r-xp)", ".rodata (r--p)", ".data (rw-p)", ".bss (rw-p)", "other",
    "Huge pages (hugetlb)", "Other", "Nameless",
]
CAT_RANK = {n: i for i, n in enumerate(CATEGORIES)}
SUB_RANK = {n: i for i, n in enumerate(SUBGROUP_ORDER)}
ARENA_SIZE_64 = 64 * 1024 * 1024   # glibc HEAP_MAX_SIZE
ARENA_SIZE_32 = 1024 * 1024
MALLOC_MMAP_MIN = 132 * 1024       # smallest mmap()ed chunk with the default 128 kB threshold
MAX_GUARD = 1024 * 1024
SYMBOL_MIN_SIZE = 4096             # -g: only symbols larger than this (bytes)

BSS_RE = re.compile(r"^\[anon:\s*glibc:\s*\.bss\s+(.+)\]$")
ARENA_RE = re.compile(r"^\[anon:\s*glibc:\s*malloc arena\b")
LOADER_RE = re.compile(r"^\[anon:\s*glibc:\s*loader malloc\b")
MALLOC_RE = re.compile(r"^\[anon:\s*glibc:\s*malloc\b")
PTHREAD_RE = re.compile(r"^\[anon:\s*glibc:\s*pthread stack")
HUGETLB_ANON_RE = re.compile(r"^/anon_hugepage( \(deleted\))?$")


def hugetlb_kb(m):
    """kB of the hugetlb pages of m, which smaps does not count in Rss"""
    return m.fields.get("Private_Hugetlb", 0) + m.fields.get("Shared_Hugetlb", 0)


class Mapping:
    __slots__ = ("start", "end", "perms", "offset", "name", "fields", "start_n", "end_n", "path", "paths",
                 "reason", "clean", "dirty", "uss", "shared", "rss", "pss", "proc", "node", "runs", "ref", "unref")

    def __init__(self, start, end, perms, offset, name):
        self.start, self.end, self.perms, self.name = start, end, perms, name
        self.offset = int(offset, 16)
        self.start_n, self.end_n = int(start, 16), int(end, 16)
        self.fields = {}
        self.paths = {}
        self.path = self.reason = self.proc = self.node = None
        self.runs = None          # referenced [(start, end)] from pagemap, None: not known
        self.clean = self.dirty = self.uss = self.shared = self.rss = self.pss = self.ref = self.unref = 0

    @property
    def range(self):
        return "%s-%s %s" % (self.start, self.end, self.perms)


class MapList(list):
    """The mappings of one process, and its pagemap ranges: checked [(start, end)] and the
    referenced runs [(start, end)] (pages present in RAM or swapped out) inside of them.
    kinds: [(start, end, kind)] runs of referenced pages that are not normal 4K pages (PAGE_KINDS), None:
    not known; pfn: kinds has every type (from /proc/kpageflags), otherwise only the swapped out pages."""
    def __init__(self):
        super().__init__()
        self.checked, self.ref = [], []
        self.kinds, self.pfn = None, False
        self.kind_starts = []
        self.ksm_ignored = None   # (pages flagged KSM, pages merged by KSM) when the KSM flag was ignored


class Proc:
    def __init__(self, pid, prog, exe, maps):
        self.pid, self.prog, self.exe, self.maps = pid, prog, exe, maps
        self.label = "%s[%s]" % (prog, pid)
        self.count = len(maps)
        self.rss = self.pss = self.shared = self.clean = self.dirty = self.uss = 0
        self.hp_private = self.hp_shared = 0      # kB of hugetlb pages (Private_Hugetlb, Shared_Hugetlb)
        self.thp = 0                              # kB of transparent huge pages (AnonHugePages + *PmdMapped)
        self.symbols = []
        self.mallinfo = None      # {field: bytes} from read_mallinfo()


# ---------- input ----------

def parse_smaps(lines, by_pid, pid=None):
    """Adds the mappings of an smaps file or of a dump with "==> /proc/<pid>/smaps <==" sections."""
    lst = by_pid.setdefault(pid, MapList()) if pid is not None else None
    cur = None
    for line in lines:
        line = line.rstrip("\r\n")
        c = line[:1]
        if "A" <= c <= "Z":                       # field lines start with an upper-case letter
            if cur is not None and line.endswith(" kB"):
                key, _, val = line.partition(":")
                if key in KEEP_FIELDS:
                    cur.fields[key] = int(val.split()[0])
            continue
        if c == "#":
            if lst is None:
                continue
            s = line.strip()
            p = PAGEMAP_RE.match(s)
            if p:
                (lst.checked if p.group(1) == "pagemap" else lst.ref).append(
                    (int(p.group(2), 16), int(p.group(3), 16)))
                continue
            p = PAGEKIND_RE.match(s)
            if p and lst.kinds is not None and p.group(3) in PAGE_KINDS:
                lst.kinds.append((int(p.group(1), 16), int(p.group(2), 16), p.group(3)))
                continue
            p = PAGEKINDS_RE.match(s)
            if p:
                lst.kinds, lst.pfn = [], p.group(1) == "pfn"
            continue
        if line.startswith("==> "):
            p = PROC_RE.match(line)
            lst = by_pid.setdefault(p.group(1), MapList()) if p else MapList()   # /proc/self etc.
            cur = None
            continue
        h = HEADER_RE.match(line)
        if not h:
            continue
        if lst is None:
            lst = by_pid.setdefault("0", MapList())
        cur = Mapping(h.group(1), h.group(2), h.group(3), h.group(4), h.group(7).strip())
        lst.append(cur)


def open_text(path):
    if path == "-":
        return sys.stdin
    opener = {".xz": lzma.open, ".lzma": lzma.open, ".gz": gzip.open, ".bz2": bz2.open}.get(
        os.path.splitext(path)[1].lower(), open)
    return opener(path, "rt", errors="replace")


def read_file(path):
    by_pid = OrderedDict()
    digits = re.findall(r"\d+", os.path.basename(path))
    with open_text(path) as f:
        head = []
        for line in f:                            # peek: a dump starts its sections with "==> "
            head.append(line)
            if line.startswith("==> ") or HEADER_RE.match(line):
                break
        system = bool(head) and head[-1].startswith("==> ")
        fallback = None if system else (digits[-1] if digits else "0")

        def lines():
            yield from head
            yield from f
        parse_smaps(lines(), by_pid, fallback)
    return by_pid, system


PAGEMAP_CHUNK = 65536                         # pages per read of /proc/<pid>/pagemap
# the top byte of a pagemap entry: bit 63 present in RAM, bit 62 swapped out
TOUCHED_TABLE = bytes(1 if b & 0xC0 else 0 for b in range(256))
TOUCHED_RUN_RE = re.compile(b"\x01+")


def touched_runs(f, start, end, page):
    """[(start, end)] runs of the pages of start..end present in RAM or swapped out, None if not readable"""
    runs = []
    p, last = start // page, end // page
    while p < last:
        n = min(PAGEMAP_CHUNK, last - p)
        try:
            f.seek(p * 8)
            data = f.read(n * 8)
        except OSError:
            return None
        if len(data) < n * 8:
            return None
        for r in TOUCHED_RUN_RE.finditer(data[7::8].translate(TOUCHED_TABLE)):
            a, b = (p + r.start()) * page, (p + r.end()) * page
            if runs and runs[-1][1] == a:
                runs[-1] = (runs[-1][0], b)
            else:
                runs.append((a, b))
        p += n
    return runs


PFN_MASK = (1 << 55) - 1
# /proc/kpageflags bits, in the order of precedence of the page types
KPF_KINDS = [(17, "huge"), (22, "thp"), (33, "locked"), (21, "ksm"), (24, "zero"), (7, "slab")]
KPAGEFLAGS_SPAN = 512                         # PFNs read at once from /proc/kpageflags


def open_kpageflags():
    try:
        return open("/proc/kpageflags", "rb")
    except OSError:
        return None


def kpage_flags(kpf, pfns):
    """{pfn: flags} from /proc/kpageflags; nearby PFNs are read together"""
    flags, pfns = {}, sorted(set(pfns))
    i = 0
    while i < len(pfns):
        j = i
        while j + 1 < len(pfns) and pfns[j + 1] - pfns[i] < KPAGEFLAGS_SPAN:
            j += 1
        kpf.seek(pfns[i] * 8)
        data = kpf.read((pfns[j] - pfns[i] + 1) * 8)
        for k in range(i, j + 1):
            o = (pfns[k] - pfns[i]) * 8
            if o + 8 <= len(data):
                flags[pfns[k]] = struct.unpack_from("<Q", data, o)[0]
        i = j + 1
    return flags


def page_kinds(f, kpf, runs, page, ksm_ok=None):
    """([(start, end, kind)] runs of the pages of runs that are not normal 4K pages, True if they have
    every page type) - without readable PFNs or kpf only the swapped out pages are found.
    ksm_ok(pages flagged KSM): False to ignore the KSM flag (see ksm_checker)."""
    found, present = {}, []                   # {address: kind}, [(address, pfn)]
    use_pfn = kpf is not None
    for s, e in runs:
        p, last = s // page, e // page
        while p < last:
            n = min(PAGEMAP_CHUNK, last - p)
            f.seek(p * 8)
            data = f.read(n * 8)
            if use_pfn:
                for i, v in enumerate(struct.unpack("<%dQ" % (len(data) // 8), data)):
                    if v & PM_SWAPPED:
                        found[(p + i) * page] = "swap"
                    elif v & PM_PRESENT:
                        pfn = v & PFN_MASK
                        if not pfn:                   # PFNs are hidden without CAP_SYS_ADMIN
                            use_pfn = False
                            present = []
                            break
                        present.append(((p + i) * page, pfn))
            if not use_pfn:
                for r in SWAPPED_RUN_RE.finditer(data[7::8].translate(SWAPPED_TABLE)):
                    for k in range(r.start(), r.end()):
                        found[(p + k) * page] = "swap"
            p += n
    if use_pfn and present:
        flags = kpage_flags(kpf, (pfn for _, pfn in present))
        kinds = KPF_KINDS
        if ksm_ok is not None:
            ksm_pages = sum(1 for _, pfn in present if first_kind(flags.get(pfn, 0), KPF_KINDS) == "ksm")
            if ksm_pages and not ksm_ok(ksm_pages):
                kinds = [(b, k) for b, k in KPF_KINDS if k != "ksm"]
        for a, pfn in present:
            kind = first_kind(flags.get(pfn, 0), kinds)
            if kind is not None:
                found[a] = kind
    out = []
    for a, kind in sorted(found.items()):
        if out and out[-1][2] == kind and out[-1][1] == a:
            out[-1] = (out[-1][0], a + page, kind)
        else:
            out.append((a, a + page, kind))
    return out, use_pfn


def first_kind(flags, kinds):
    for bit, kind in kinds:
        if flags >> bit & 1:
            return kind
    return None


KSM_SLACK = 1.1     # pages flagged KSM may exceed ksm_merging_pages a little (both are sampled at different times)


def read_int(path):
    try:
        with open(path) as f:
            return int(f.read().split()[0])
    except (OSError, ValueError, IndexError):
        return None


def ksm_checker(pid, maps):
    """ksm_ok(pages flagged KSM): False when /proc/kpageflags reports more KSM pages than the process
    has merged by KSM (/proc/<pid>/ksm_merging_pages), i.e. the kernel bug of Linux 6.10 - 7.2-rc2
    (fixed by 81401cebfc15 "fs/proc: fix KPF_KSM reported for all anonymous pages") that flags every
    anonymous page as KSM; sets maps.ksm_ignored = (flagged pages, merged pages) then."""
    def ksm_ok(flagged):
        merging = read_int("/proc/%s/ksm_merging_pages" % pid)
        if merging is None:                   # kernel < 6.1, older than the bug
            return True
        if read_int("/sys/kernel/mm/ksm/run") == 0:
            merging = 0
        if flagged <= merging * KSM_SLACK + 16:
            return True
        maps.ksm_ignored = (flagged, merging)
        return False
    return ksm_ok


SWAPPED_TABLE = bytes(1 if b & 0x40 else 0 for b in range(256))
SWAPPED_RUN_RE = re.compile(b"\x01+")


def read_pagemap(pid, maps, kpf=None):
    """Fills maps.checked and maps.ref for every mapping but the ---p reservations; those without
    resident or swapped pages, or with only such pages, are taken from smaps. Also fills maps.kinds
    (maps.pfn: with kpf, the open /proc/kpageflags, and visible PFNs)."""
    checked, ref = [], []
    with open("/proc/%s/pagemap" % pid, "rb") as f:
        for m in maps:
            if m.perms[:3] == "---":
                continue
            s, e = m.start_n, m.end_n
            touched = (m.fields.get("Rss", 0) + m.fields.get("Swap", 0) + hugetlb_kb(m)) * 1024
            if touched == 0:
                runs = []
            elif touched >= e - s:
                runs = [(s, e)]
            else:
                runs = touched_runs(f, s, e, PAGE)
                if runs is None:
                    continue
            checked.append((s, e))
            ref.extend(runs)
        maps.checked, maps.ref = checked, ref
        try:
            maps.kinds, maps.pfn = page_kinds(f, kpf, ref, PAGE, ksm_checker(pid, maps))
        except OSError:
            maps.kinds, maps.pfn = None, False


def read_live(pids, dump=None):
    """dump: file object receiving the raw smaps, in `tail -n +1 /proc/*/smaps` format
    when more than one process is read (so it can be loaded again with -i), with the pagemap
    ranges appended as "# mtrace pagemap|referenced <start> <end>" lines.
    Returns (by_pid, skipped [(pid, reason)], [pids whose pagemap is not readable])."""
    by_pid = OrderedDict()
    skipped, no_pagemap = [], []
    kpf = open_kpageflags()
    for pid in pids:
        try:
            with open("/proc/%s/smaps" % pid, errors="replace") as f:
                text = f.read()
            parse_smaps(text.splitlines(), by_pid, str(pid))
            maps = by_pid[str(pid)]
            if maps:
                try:
                    read_pagemap(pid, maps, kpf)
                except OSError:
                    no_pagemap.append(pid)
            if dump is not None and text:
                if len(pids) > 1:
                    dump.write("%s==> /proc/%s/smaps <==\n" % ("\n" if dump.tell() else "", pid))
                dump.write(text if text.endswith("\n") else text + "\n")
                dump.writelines("# mtrace pagemap 0x%x 0x%x\n" % r for r in maps.checked)
                dump.writelines("# mtrace referenced 0x%x 0x%x\n" % r for r in maps.ref)
                if maps.kinds is not None:
                    dump.write("# mtrace pagekinds %s\n" % ("pfn" if maps.pfn else "nopfn"))
                    dump.writelines("# mtrace pagekind 0x%x 0x%x %s\n" % r for r in maps.kinds)
        except FileNotFoundError:
            skipped.append((pid, "process vanished"))
        except PermissionError:
            skipped.append((pid, "permission denied"))
        except OSError as e:
            skipped.append((pid, e.strerror or str(e)))
    if kpf is not None:
        kpf.close()
    return by_pid, skipped, no_pagemap


def all_pids():
    me = os.getpid()
    return sorted(int(d) for d in os.listdir("/proc") if d.isdigit() and int(d) != me)


def comm_of(pid):
    try:
        with open("/proc/%s/comm" % pid) as f:
            return f.read().strip()
    except OSError:
        return None


# ---------- classification ----------

def strip_deleted(p):
    return p[:-10] if p.endswith(" (deleted)") else p


def basename(p):
    s = strip_deleted(p)
    return s[s.rfind("/") + 1:] or s


def make_labeler(paths):
    """basename, or the full path when two different files share a basename"""
    count = {}
    for p in {strip_deleted(p) for p in paths}:
        b = basename(p)
        count[b] = count.get(b, 0) + 1

    def label(p):
        s = basename(p) if count.get(basename(p)) == 1 else strip_deleted(p)
        return s + " (deleted)" if p.endswith(" (deleted)") else s
    return label


def section_for(perms):
    if perms[2] == "x":
        return ".text (%s)" % perms
    return {"r--p": ".rodata (r--p)", "rw-p": ".data (rw-p)"}.get(perms, "other")


def classify(maps, label):
    """Classifies one process (maps sorted by address); returns the main executable path."""
    exec_files = OrderedDict((m.name, None) for m in maps if m.name.startswith("/") and m.perms[2] == "x")
    # the program binary is the lowest mapped ELF object; every other one is a dynamic library
    main = next((m.name for m in maps if m.name in exec_files), None)

    def exec_path(f, section):
        return ["Executable", "Binary" if f == main else "Dynamic libraries", label(f), section]

    def put(m, path, reason):
        m.path, m.reason = path, reason

    def free(m):
        return m.path is None and m.name == ""

    # glibc names .bss after the soname, which may be a prefix of the mapped file (libX.so.67 vs libX.so.67.16.0)
    def bss_owner(f, prev):
        if f in exec_files:
            return f
        for e in exec_files:
            if e.startswith(f + "."):
                return e
        return prev.name if prev is not None and prev.name in exec_files else None

    for i, m in enumerate(maps):
        n = m.name
        if n == "":
            continue
        bss = BSS_RE.match(n)
        owner = bss and bss_owner(bss.group(1), maps[i - 1] if i else None)
        if owner:
            put(m, exec_path(owner, ".bss (rw-p)"), "named by glibc")
        elif n == "[heap]":
            put(m, ["Dynamic allocator", "Heap"], "brk() heap of the main arena")
        elif n.startswith("[stack"):
            put(m, ["Thread stack", "main stack"], "main thread stack")
        elif ARENA_RE.match(n):
            put(m, ["Dynamic allocator", "glibc malloc arena"], "named by glibc")
        elif LOADER_RE.match(n):
            put(m, ["Dynamic allocator", "glibc loader malloc"], "named by glibc (ld.so loader)")
        elif MALLOC_RE.match(n):
            put(m, ["Dynamic allocator", "glibc malloc"], "named by glibc")
        elif PTHREAD_RE.match(n):
            put(m, ["Thread stack", "pthread stack"], "named by glibc")
        elif n.startswith("["):
            put(m, ["Anonymous", "Other", n], "named kernel / anonymous mapping")
        elif HUGETLB_ANON_RE.match(n):
            put(m, ["Anonymous", "Huge pages (hugetlb)", m.perms],
                "anonymous hugetlb mapping (MAP_HUGETLB, %d kB pages)" % m.fields.get("KernelPageSize", 0))
        elif n in exec_files:
            put(m, exec_path(n, section_for(m.perms)), "%s file mapping of an ELF object" % m.perms)
        else:
            put(m, ["File Backed", label(n), m.perms], "file mapping without executable segment")

    is32bit = all(m.name == "[vsyscall]" or m.end_n <= 2 ** 32 for m in maps)
    size = ARENA_SIZE_32 if is32bit else ARENA_SIZE_64
    for i, m in enumerate(maps):
        if not free(m) or m.perms != "rw-p" or m.start_n % size:
            continue
        j, end = i, m.end_n
        while (end - m.start_n < size and j + 1 < len(maps) and maps[j + 1].start_n == end and
               free(maps[j + 1]) and maps[j + 1].perms == "---p"):
            j += 1
            end = maps[j].end_n
        if end - m.start_n == size:
            for k in range(i, j + 1):
                put(maps[k], ["Dynamic allocator", "glibc malloc arena"],
                    "anonymous %d MB-aligned rw-p + ---p reservation (thread arena heap)" % (size // 1048576))

    for i in range(1, len(maps)):
        m, p = maps[i], maps[i - 1]
        if free(m) and m.perms == "rw-p" and p.end_n == m.start_n and p.name in exec_files and p.perms == "rw-p":
            put(m, exec_path(p.name, ".bss (rw-p)"), "anonymous rw-p directly after .data of %s" % basename(p.name))

    for i in range(1, len(maps)):
        m, g = maps[i], maps[i - 1]
        if (free(m) and m.perms == "rw-p" and free(g) and g.perms == "---p" and
                g.end_n == m.start_n and g.end_n - g.start_n <= MAX_GUARD):
            put(m, ["Thread stack", "pthread stack"], "anonymous rw-p directly above a ---p guard (pthread stack)")
            put(g, ["Thread stack", "stack guard (---p)"], "guard page of a pthread stack")

    for m in maps:
        if m.path is not None:
            continue
        if m.perms == "rw-p" and m.end_n - m.start_n >= MALLOC_MMAP_MIN:
            put(m, ["Dynamic allocator", "glibc malloc"], "anonymous rw-p \u2265 132 kB (likely a malloc mmap() chunk)")
        else:
            put(m, ["Anonymous", "Nameless", m.perms], "anonymous mapping")
    return main


def assign_runs(maps):
    """m.runs of the mappings covered by a checked pagemap range of maps (sorted by address);
    m.ref / m.unref: their referenced and not referenced kB (from Rss + Swap without pagemap)."""
    checked, ref = sorted(maps.checked), sorted(maps.ref)
    cs, rs = [c[0] for c in checked], [r[0] for r in ref]
    if maps.kinds is not None:
        maps.kinds.sort()
        maps.kind_starts = [k[0] for k in maps.kinds]
    for m in maps:
        m.runs = None
        i = bisect.bisect_right(cs, m.start_n) - 1
        if i >= 0 and checked[i][1] >= m.end_n:
            m.runs = []
            j = max(0, bisect.bisect_right(rs, m.start_n) - 1)
            while j < len(ref) and ref[j][0] < m.end_n:
                s, e = max(ref[j][0], m.start_n), min(ref[j][1], m.end_n)
                j += 1
                if s < e:
                    m.runs.append((s, e))
        if m.perms[:3] == "---":
            m.ref = m.unref = 0
            continue
        size = (m.end_n - m.start_n) // 1024
        if m.runs is not None:
            m.ref = sum(e - s for s, e in m.runs) // 1024
        else:
            m.ref = min(size, m.fields.get("Rss", 0) + m.fields.get("Swap", 0) + hugetlb_kb(m))
        m.unref = size - m.ref


def analyze(by_pid, layouts, live):
    """Classifies every process once per layout into m.paths[layout]: the "grouped" view labels files
    by the files of all processes, the "program" (and single-process) view by those of their own process."""
    files = {m.name for maps in by_pid.values() for m in maps if m.name.startswith("/")}
    global_label = make_labeler(files)
    procs = []
    for pid, maps in by_pid.items():
        if not maps:
            continue                              # kernel threads
        maps.sort(key=lambda m: m.start_n)
        assign_runs(maps)
        own_label = make_labeler({m.name for m in maps if m.name.startswith("/")})
        exe = None
        for layout in layouts:
            for m in maps:
                m.path = None
            exe = classify(maps, global_label if layout == "grouped" else own_label)
            for m in maps:
                m.paths[layout] = m.path
        prog = basename(exe) if exe else ((live and comm_of(pid)) or "?")
        proc = Proc(int(pid) if pid.isdigit() else pid, prog, exe or "", maps)
        proc.cmd = (live and comm_of(pid)) or prog
        procs.append(proc)
        for m in maps:
            f = m.fields
            m.clean = f.get("Private_Clean", 0)
            m.dirty = f.get("Private_Dirty", 0)
            m.uss = m.clean + m.dirty
            m.shared = f.get("Shared_Clean", 0) + f.get("Shared_Dirty", 0)
            m.rss = f.get("Rss", 0)
            m.pss = f.get("Pss", 0)
            m.proc = proc
            proc.rss += m.rss
            proc.pss += m.pss
            # hugetlb pages are not in Rss / Pss / Private_* / Shared_*, only in *_Hugetlb
            proc.hp_private += f.get("Private_Hugetlb", 0)
            proc.hp_shared += f.get("Shared_Hugetlb", 0)
            # transparent huge pages are part of Rss / USS
            proc.thp += f.get("AnonHugePages", 0) + f.get("ShmemPmdMapped", 0) + f.get("FilePmdMapped", 0)
            proc.shared += m.shared
            proc.clean += m.clean
            proc.dirty += m.dirty
            proc.uss += m.uss
    return procs


def use_layout(procs, layout):
    for p in procs:
        for m in p.maps:
            m.path = m.paths[layout]


# ---------- tree ----------

class Node:
    __slots__ = ("name", "kind", "parent", "children", "child_map", "clean", "dirty", "count",
                 "self_clean", "self_dirty", "self_count", "full_path", "proc", "mapping", "sym", "run")

    def __init__(self, name, kind, parent):
        self.name, self.kind, self.parent = name, kind, parent
        self.children, self.child_map = [], {}
        self.clean = self.dirty = self.count = 0
        self.self_clean = self.self_dirty = self.self_count = 0
        self.full_path = self.proc = self.mapping = self.sym = self.run = None

    @property
    def value(self):
        return self.clean + self.dirty

    def child(self, name, kind, key=None):
        key = name if key is None else key
        c = self.child_map.get(key)
        if c is None:
            c = Node(name, kind, self)
            self.child_map[key] = c
            self.children.append(c)
        return c


# Referenced pages view: clean = referenced kB, dirty = not referenced kB
MAX_RUNS = 64          # more runs in a mapping: split it into BLOCKS blocks
BLOCK_RUNS = 16        # more runs in a block: split it again
BLOCKS = 16
MAX_DETAIL_RUNS = 32768   # more runs in a mapping: blocks of up to MIN_BLOCK_PAGES only show their totals
MIN_BLOCK_PAGES = 64


def estimate_kinds(m, kb, with_swap):
    """{kind: kB} of kb referenced kB of m estimated from its smaps counters (with_swap: the kB include
    swapped out pages); same precedence as KPF_KINDS: huge > THP > locked"""
    f = m.fields
    rss, swap = f.get("Rss", 0), f.get("Swap", 0)
    out = OrderedDict()
    if with_swap and rss + swap > 0:
        out["swap"] = min(kb, round(kb * swap / (rss + swap)))
        kb -= out["swap"]
    if f.get("KernelPageSize", 4) > 4:
        out["huge"] = kb
        return out
    if rss > 0:
        thp = min(rss, f.get("AnonHugePages", 0) + f.get("ShmemPmdMapped", 0) + f.get("FilePmdMapped", 0))
        out["thp"] = min(kb, round(kb * thp / rss))
        out["locked"] = min(kb - out["thp"], round(kb * max(0, min(f.get("Locked", 0), rss) - thp) / rss))
        kb -= out["thp"] + out["locked"]
    out["4k"] = kb
    return out


def kind_split(maps, m, s, e):
    """{(kind, estimated): kB} of the referenced pages s..e of mapping m"""
    out = OrderedDict()

    def add(key, kb):
        if kb > 0:
            out[key] = out.get(key, 0) + kb
    total = (e - s) // 1024
    if maps.kinds is None:
        for k, kb in estimate_kinds(m, total, True).items():
            add((k, True), kb)
        return out
    exact = 0
    i = max(0, bisect.bisect_right(maps.kind_starts, s) - 1)
    while i < len(maps.kinds) and maps.kinds[i][0] < e:
        a, b, k = maps.kinds[i]
        i += 1
        a, b = max(a, s), min(b, e)
        if a < b:
            add((k, False), (b - a) // 1024)
            exact += (b - a) // 1024
    if maps.pfn:
        add(("4k", False), total - exact)
    else:
        for k, kb in estimate_kinds(m, total - exact, False).items():
            add((k, True), kb)
    return out


def add_kinds(node, counts, proc):
    """One child of node per page type of counts {(kind, estimated): kB}"""
    for (k, est), kb in counts.items():
        if kb > 0:
            c = node.child(PAGE_KINDS[k] + (" (estimated)" if est else ""), "pk_" + k)
            c.self_clean += kb
            c.proc = proc


def add_runs(node, start, end, runs, proc, max_runs=MAX_RUNS, detail=None, split=None):
    """The referenced runs [(s, e)] (sorted, inside start..end) and the not referenced gaps between
    them as children of node in address order; split(s, e): the page types of a referenced run
    ({(kind, estimated): kB}), shown below its node."""
    segs, pos = [], start
    for s, e in runs:
        if s > pos:
            segs.append((pos, s, False))
        segs.append((s, e, True))
        pos = e
    if pos < end:
        segs.append((pos, end, False))
    if detail is None:
        detail = len(segs) <= MAX_DETAIL_RUNS
    if len(segs) <= max_runs:
        for s, e, rf in segs:
            c = node.child("referenced" if rf else "not referenced", "ref" if rf else "unref", s)
            c.run, c.proc = (s, e), proc
            if not rf:
                c.self_dirty += (e - s) // 1024
            elif split is not None:
                add_kinds(c, split(s, e), proc)
            else:
                c.self_clean += (e - s) // 1024
        return
    pages = (end - start) // PAGE
    if not detail and pages <= MIN_BLOCK_PAGES:
        ref = sum(e - s for s, e, rf in segs if rf) // 1024
        n = sum(1 for _, _, rf in segs if rf)
        c = node.child("referenced (%d runs)" % n, "ref")
        c.proc = proc
        if split is not None:
            counts = OrderedDict()
            for s, e, rf in segs:
                if rf:
                    for k, kb in split(s, e).items():
                        counts[k] = counts.get(k, 0) + kb
            add_kinds(c, counts, proc)
        else:
            c.self_clean = ref
        c = node.child("not referenced (%d runs)" % (len(segs) - n), "unref")
        c.self_dirty, c.proc = (end - start) // 1024 - ref, proc
        return
    step = max(-(-pages // BLOCKS), 1 if detail else MIN_BLOCK_PAGES) * PAGE
    for b in range(start, end, step):
        be = min(b + step, end)
        c = node.child("%x-%x" % (b, be), "block")
        c.run, c.proc = (b, be), proc
        add_runs(c, b, be, [(max(s, b), min(e, be)) for s, e in runs if s < be and e > b], proc, BLOCK_RUNS, detail,
                 split)


def page_owners(proc):
    """(sorted pages, their symbols): every page of a symbol is owned by the symbol covering most of it"""
    best = {}
    for s in proc.symbols:
        for p in range(s.addr // PAGE, (s.addr + s.size - 1) // PAGE + 1):
            cover = min(s.addr + s.size, (p + 1) * PAGE) - max(s.addr, p * PAGE)
            if p not in best or cover > best[p][0]:
                best[p] = (cover, s)
    pages = sorted(best)
    return pages, [best[p][1] for p in pages]


def add_symbol_runs(node, m, owners, proc, split=None):
    """The pages of m in address order: those of a symbol below a node of the symbol, the others
    directly below node."""
    pages, syms = owners
    pieces, pos = [], m.start_n          # (start, end, symbol or None)
    i = bisect.bisect_left(pages, m.start_n // PAGE)
    while i < len(pages) and pages[i] < m.end_n // PAGE:
        a, s = pages[i] * PAGE, syms[i]
        i += 1
        if a > pos:
            pieces.append((pos, a, None))
        if pieces and pieces[-1][2] is s and pieces[-1][1] == a:
            pieces[-1] = (pieces[-1][0], a + PAGE, s)
        else:
            pieces.append((a, a + PAGE, s))
        pos = a + PAGE
    if pos < m.end_n:
        pieces.append((pos, m.end_n, None))
    for a, b, s in pieces:
        runs = [(max(x, a), min(y, b)) for x, y in m.runs if x < b and y > a]
        if s is None:
            add_runs(node, a, b, runs, proc, split=split)
            continue
        c = node.child("%s @%x" % (s.name, s.addr) if s.name in node.child_map and node.child_map[s.name].sym is not s
                       else s.name, "sym")
        if c.sym is None:
            c.sym, c.proc, c.full_path, c.run = s, proc, s.elf, (a, b)
            s.nodes.append(c)
        else:
            c.run = (c.run[0], b)
        add_runs(c, a, b, runs, proc, split=split)


def add_referenced(node, m, segments, proc, owners=None):
    """The referenced and not referenced pages of m below node; every referenced node is split by
    page type (4K, THP, huge, locked, KSM, slab, zero, swapped out)."""
    def split(s, e):
        return kind_split(proc.maps, m, s, e)
    if segments and m.runs is not None:
        if owners and owners[0]:
            add_symbol_runs(node, m, owners, proc, split)
        else:
            add_runs(node, m.start_n, m.end_n, m.runs, proc, split=split)
        return
    est = "" if m.runs is not None else " (estimated from smaps)"
    if m.ref > 0:
        c = node.child("referenced" + est, "ref")
        c.proc = proc
        if m.runs is None:
            add_kinds(c, OrderedDict(((k, True), kb) for k, kb in estimate_kinds(m, m.ref, True).items()), proc)
        else:
            counts = OrderedDict()
            for s, e in m.runs:
                for k, kb in split(s, e).items():
                    counts[k] = counts.get(k, 0) + kb
            add_kinds(c, counts, proc)
    if m.unref > 0:
        c = node.child("not referenced" + est, "unref")
        c.self_dirty += m.unref
        c.proc = proc


def build_tree(procs, single, layout, segments, metric="uss"):
    """metric "uss": the USS of the mappings; "referenced": their size (without the ---p reservations)
    split into referenced and not referenced pages."""
    ref_view = metric == "referenced"
    root = Node("all (referenced pages)" if ref_view else "all (USS)", "root", None)
    program = not single and layout == "program"
    for proc in procs:
        for m in proc.maps:
            m.node = None
        owners = None
        if ref_view:
            for s in proc.symbols:
                s.nodes = []
            if segments and proc.symbols:
                owners = page_owners(proc)
        for m in proc.maps:
            if (m.ref + m.unref if ref_view else m.uss) <= 0:
                continue
            if single:
                path, proc_depth = m.path, -1
            elif program:
                path, proc_depth = [proc.label] + m.path, 0
            else:
                proc_depth = PROC_DEPTH.get(m.path[0], 1)
                path = m.path[:proc_depth] + [proc.label] + m.path[proc_depth:]
            cat = 1 if program else 0
            kind = CATEGORY_KIND[path[cat]]
            # level holding the binary / library / file name (Executable > Binary|Dynamic libraries > <name>)
            name_idx = cat + (2 if path[cat] == "Executable" else 1)
            node = root
            for i, name in enumerate(path):
                node = node.child(name, "proc" if i == proc_depth else kind)
                if i == proc_depth:
                    node.proc, node.full_path = proc, proc.exe
                elif i == name_idx and m.name.startswith("/"):
                    node.full_path = m.name
                elif 0 <= proc_depth < i:
                    node.proc = proc
            if segments:
                node = node.child(m.range, kind)
                node.mapping, node.proc, node.full_path = m, proc, m.name
            if ref_view:
                add_referenced(node, m, segments, proc, owners)
            else:
                node.self_clean += m.clean
                node.self_dirty += m.dirty
            node.self_count += 1
            m.node = node
    return root


def finalize(root):
    order, stack = [], [root]
    while stack:
        n = stack.pop()
        order.append(n)
        stack.extend(n.children)
    for n in reversed(order):
        n.clean, n.dirty, n.count = n.self_clean, n.self_dirty, n.self_count
        for c in n.children:
            n.clean += c.clean
            n.dirty += c.dirty
            n.count += c.count

        def rank(c):
            r = (CAT_RANK if c.name in CAT_RANK else SUB_RANK).get(c.name)
            return float("inf") if r is None or c.mapping is not None else r
        n.children.sort(key=lambda c: (rank(c), c.run[0] if c.run is not None else -c.value))


# ---------- symbols (global variables, from nm + /proc/<pid>/pagemap) ----------

PAGE = os.sysconf("SC_PAGE_SIZE")
PM_PRESENT = 1 << 63
PM_SWAPPED = 1 << 62
PM_FILE = 1 << 61
PM_EXCLUSIVE = 1 << 56
VARIABLE_TYPES = "dDbBrR"
SECTION_RE = re.compile(r"\]\s+(\S+)\s+\S+\s+([0-9a-fA-F]+)\s+[0-9a-fA-F]+\s+([0-9a-fA-F]+)")


class Symbol:
    __slots__ = ("elf", "name", "typ", "section", "addr", "size", "pages", "resident", "swap",
                 "clean", "dirty", "owned", "nodes", "home")

    def __init__(self, elf, name, typ, section, addr, size):
        self.elf, self.name, self.typ, self.section, self.addr, self.size = elf, name, typ, section, addr, size
        self.pages = (addr + size - 1) // PAGE - addr // PAGE + 1
        self.resident = self.swap = self.clean = self.dirty = 0   # bytes / kB (clean, dirty)
        self.owned = []          # (page, file backed) of the private pages attributed to this symbol
        self.nodes = []
        self.home = None

    @property
    def referenced(self):
        """share of the symbol's pages that are present in RAM, i.e. were touched (read or written)"""
        return self.resident / (self.pages * PAGE)


def elf_is_exec(path):
    with open(path, "rb") as f:
        hdr = f.read(18)
    return struct.unpack_from("<H", hdr, 16)[0] == 2  # ET_EXEC: absolute addresses


def elf_sections(path):
    """[(start, size, name)] of the allocated sections, sorted by address"""
    out = subprocess.run(["readelf", "-SW", path], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                         universal_newlines=True, check=True).stdout
    spans = []
    for line in out.splitlines():
        m = SECTION_RE.search(line)
        if m and int(m.group(2), 16):
            spans.append((int(m.group(2), 16), int(m.group(3), 16), m.group(1)))
    return sorted(spans)


def section_of(spans, starts, addr):
    i = bisect.bisect_right(starts, addr) - 1
    if i >= 0 and addr < spans[i][0] + max(spans[i][1], 1):
        return spans[i][2]
    return "?"


def nm_symbols(path, all_types):
    out = subprocess.run(["nm", "-S", "-C", "--defined-only", path], stdout=subprocess.PIPE,
                         stderr=subprocess.DEVNULL, universal_newlines=True, check=True).stdout
    for line in out.splitlines():
        parts = line.split(None, 3)
        if len(parts) < 4:
            continue
        addr, size, typ, name = parts
        if all_types or typ in VARIABLE_TYPES:
            yield int(addr, 16), int(size, 16), typ, name


def symbol_elfs(proc, wanted):
    """ELF files to inspect: the main executable ([]), every mapped ELF object (["all"]) or the given files"""
    mapped = OrderedDict((strip_deleted(m.name), None) for m in proc.maps
                         if m.name.startswith("/") and m.perms[2] == "x")
    if not wanted:
        return [proc.exe] if proc.exe else []
    if wanted == ["all"]:
        return list(mapped)
    by_real = {os.path.realpath(p): p for p in mapped}
    return [by_real.get(os.path.realpath(w), w) for w in wanted]


def load_bias(proc, path, warn):
    if elf_is_exec(path):
        return 0
    real = os.path.realpath(path)
    for m in proc.maps:
        if m.name.startswith("/") and os.path.realpath(strip_deleted(m.name)) == real:
            return m.start_n - m.offset
    warn("%s is not mapped in process %s" % (path, proc.pid))
    return None


def read_symbols(proc, wanted, all_types, min_size, warn):
    """Fills proc.symbols with the symbols larger than min_size and their page residency. Each private
    (exclusively mapped) resident page is owned by the one symbol covering most of it, so the owned
    pages of all symbols add up to at most the USS of their mappings."""
    syms = []
    for elf in symbol_elfs(proc, wanted):
        try:
            bias = load_bias(proc, elf, warn)
            if bias is None:
                continue
            spans = elf_sections(elf)
            starts = [s[0] for s in spans]
            for addr, size, typ, name in nm_symbols(elf, all_types):
                if size > min_size:
                    syms.append(Symbol(elf, name, typ, section_of(spans, starts, addr), bias + addr, size))
        except FileNotFoundError as e:
            warn("cannot read symbols of %s: %s not found" % (elf, e.filename))
        except (OSError, subprocess.CalledProcessError) as e:
            warn("cannot read symbols of %s: %s" % (elf, e))
    if not syms:
        return
    try:
        pagemap = open("/proc/%s/pagemap" % proc.pid, "rb")
    except OSError as e:
        warn("cannot read /proc/%s/pagemap: %s" % (proc.pid, e.strerror))
        return
    flags = {}
    best = {}   # page -> (bytes of the page covered by the symbol, symbol, flags)
    with pagemap:
        for s in syms:
            first, last = s.addr // PAGE, (s.addr + s.size - 1) // PAGE
            missing = [p for p in range(first, last + 1) if p not in flags]
            if missing:
                pagemap.seek(first * 8)
                data = pagemap.read((last - first + 1) * 8)
                for i, v in enumerate(struct.unpack("<%dQ" % (len(data) // 8), data)):
                    flags[first + i] = v
            for p in range(first, last + 1):
                f = flags.get(p, 0)
                if f & PM_PRESENT:
                    s.resident += PAGE
                    if f & PM_EXCLUSIVE:
                        cover = min(s.addr + s.size, (p + 1) * PAGE) - max(s.addr, p * PAGE)
                        if p not in best or cover > best[p][0]:
                            best[p] = (cover, s, f)
                elif f & PM_SWAPPED:
                    s.swap += PAGE
    for p, (_, s, f) in sorted(best.items()):
        s.owned.append((p, bool(f & PM_FILE)))
    proc.symbols = syms


def mapping_finder(proc):
    starts = [m.start_n for m in proc.maps]

    def mapping_at(addr):
        i = bisect.bisect_right(starts, addr) - 1
        return proc.maps[i] if i >= 0 and addr < proc.maps[i].end_n else None
    return mapping_at


def home_symbols(proc):
    """Links the symbols to the node of their mapping (the symbol nodes of the referenced pages view
    are added by build_tree)."""
    mapping_at = mapping_finder(proc)
    for s in proc.symbols:
        m = mapping_at(s.addr)
        s.home = m.node if m is not None else None


def attach_symbols(proc):
    """Moves the USS of the owned pages from the mapping nodes to one child node per symbol."""
    mapping_at = mapping_finder(proc)
    per_node = OrderedDict()   # mapping node -> {symbol: [clean kB, dirty kB]}
    for s in proc.symbols:
        s.clean = s.dirty = 0
        s.nodes = []
        m = mapping_at(s.addr)
        s.home = m.node if m is not None else None
        for p, file_backed in s.owned:
            m = mapping_at(p * PAGE)
            if m is None or m.node is None:
                continue
            kb = per_node.setdefault(m.node, OrderedDict()).setdefault(s, [0, 0])
            kb[0 if file_backed else 1] += PAGE // 1024
    for node, by_sym in per_node.items():
        for s, (clean, dirty) in sorted(by_sym.items(), key=lambda kv: -sum(kv[1])):
            # smaps and pagemap are read at different times: never take more than the mapping has
            clean, dirty = min(clean, node.self_clean), min(dirty, node.self_dirty)
            if clean + dirty <= 0:
                continue
            node.self_clean -= clean
            node.self_dirty -= dirty
            # e.g. static variables of the same name in different translation units
            c = node.child("%s @%x" % (s.name, s.addr) if s.name in node.child_map else s.name, "sym")
            c.self_clean += clean
            c.self_dirty += dirty
            c.sym, c.proc, c.full_path = s, proc, s.elf
            s.clean += clean
            s.dirty += dirty
            s.nodes.append(c)


# ---------- mallinfo (glibc malloc statistics, from gdb) ----------

MALLINFO_FIELDS = ["arena", "ordblks", "smblks", "hblks", "hblkhd", "usmblks", "fsmblks", "uordblks",
                   "fordblks", "keepcost"]
MALLINFO_TIMEOUT = 60
GDB_NOISE_RE = re.compile(r"^(\[|Reading |Loaded |Using |warning: |Missing |0x[0-9a-f]+ in |$)")


def run_gdb(pid, commands, result_re):
    """Runs the gdb commands in the attached process; returns the match of result_re on gdb's output.
    Raises RuntimeError."""
    cmd = ["gdb", "-nx", "-batch", "-p", str(pid)]
    for c in commands + ["detach"]:
        cmd += ["-ex", c]
    try:
        out = subprocess.run(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             universal_newlines=True, timeout=MALLINFO_TIMEOUT).stdout
    except FileNotFoundError:
        raise RuntimeError("gdb not found")
    except subprocess.TimeoutExpired:
        # gdb was killed while attached; the process may be left stopped
        try:
            os.kill(pid, signal.SIGCONT)
        except OSError:
            pass
        raise RuntimeError("gdb timed out after %d s (process stopped inside malloc?)" % MALLINFO_TIMEOUT)
    m = result_re.search(out)
    if m:
        return m
    errors = [l for l in out.splitlines() if not GDB_NOISE_RE.match(l)]
    # a failed attach is followed by "The program is not being run." for every command
    attach = [l for l in errors if l.startswith("ptrace:") or "Could not attach" in l]
    if attach:
        why = attach[0]
        scope = read_int("/proc/sys/kernel/yama/ptrace_scope")
        if "not permitted" in why and scope and os.geteuid() != 0:
            why += " (kernel.yama.ptrace_scope = %d: only root may attach to a running process; run as root " \
                   "or: sudo sysctl kernel.yama.ptrace_scope=0)" % scope
        raise RuntimeError(why)
    raise RuntimeError(errors[-1] if errors else "no output from gdb")


MALLINFO_RE = re.compile(r"^arena=.*$", re.M)
TRIM_RE = re.compile(r"^malloc_trim=(-?\d+)$", re.M)


def read_mallinfo(pid):
    """{field: bytes} of mallinfo() called in the running process by gdb. Without glibc debug info gdb
    does not know struct mallinfo, so the struct is returned through its hidden pointer argument into
    unused stack 8 kB below $rsp. The fields are 32-bit (wrap at 4 GB). Raises RuntimeError."""
    printf = 'printf "%s\\n", %s' % (" ".join("%s=%%u" % f for f in MALLINFO_FIELDS),
                                     ", ".join("$m[%d]" % i for i in range(len(MALLINFO_FIELDS))))
    line = run_gdb(pid, ["set $m = (unsigned int *)($rsp - 0x2000)",
                         "call ((void (*)(void *))mallinfo)($m)",
                         printf], MALLINFO_RE).group(0)
    return {k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", line)}


def malloc_trim(pid):
    """Calls malloc_trim(0) in the running process by gdb; returns its result (1: memory was released
    to the system). Raises RuntimeError."""
    return int(run_gdb(pid, ["set $r = ((int (*)(unsigned long))malloc_trim)(0)",
                             'printf "malloc_trim=%d\\n", $r'], TRIM_RE).group(1))


MALLINFO_JOBS = 8
LIBC_RE = re.compile(r"/libc(-[\d.]+)?\.so")


def uid_of(pid):
    try:
        with open("/proc/%s/status" % pid) as f:
            for line in f:
                if line.startswith("Uid:"):
                    return int(line.split()[2])          # effective uid
    except (OSError, IndexError, ValueError):
        pass
    return None


def gdb_each(procs, pids, what, call):
    """call(pid) for the processes pids (all of procs: None) that can be attached, several gdb in
    parallel; returns ({pid: result}, the processes without result as {reason: [pid]})."""
    by_pid = OrderedDict((p.pid, p) for p in procs)
    failed, todo = OrderedDict(), []
    me = os.geteuid()
    for pid in (by_pid if pids is None else pids):
        p = by_pid.get(pid)
        if p is None:
            why = "not analyzed"
        elif not any(LIBC_RE.search(m.name) for m in p.maps):
            why = "glibc not mapped"
        elif me != 0 and uid_of(pid) != me:
            why = "process vanished" if uid_of(pid) is None else "process of another user"
        else:
            todo.append(p)
            continue
        failed.setdefault(why, []).append(pid)
    if len(todo) > 1:
        sys.stderr.write("%s in %d processes via gdb...\n" % (what, len(todo)))

    def run(p):
        try:
            return call(p.pid), None
        except RuntimeError as e:
            return None, str(e)
    results = OrderedDict()
    with ThreadPoolExecutor(max_workers=MALLINFO_JOBS) as ex:
        for p, (res, why) in zip(todo, ex.map(run, todo)):
            if why is None:
                results[p.pid] = res
            else:
                failed.setdefault(why, []).append(p.pid)
    return results, failed


def warn_failed(what, failed):
    for why, lst in failed.items():
        sys.stderr.write("warning: no %s of %d process(es) (%s): %s%s\n" % (
            what, len(lst), why, " ".join(map(str, lst[:20])), " ..." if len(lst) > 20 else ""))


def collect_mallinfo(procs, pids):
    """Sets p.mallinfo of the processes pids (all of procs: None)."""
    results, failed = gdb_each(procs, pids, "calling mallinfo()", read_mallinfo)
    for p in procs:
        if p.pid in results:
            p.mallinfo = results[p.pid]
    warn_failed("mallinfo()", failed)


def mallinfo_kb(mi):
    """(system, alloc, free) kB of a mallinfo() result"""
    system = mi["arena"] + mi["hblkhd"]
    alloc = mi["uordblks"] + mi["usmblks"] + mi["hblkhd"]
    free = mi["fordblks"] + mi["fsmblks"]
    return system // 1024, alloc // 1024, free // 1024


# ---------- output ----------

def tree_json(root, proc_index, sym_index, maps, map_index):
    """Returns the tree and the pre-order index of every node; appends the tooltip data of mapping
    nodes not seen yet to maps (shared by all views)."""
    node_index = {}

    def conv(n):
        node_index[id(n)] = len(node_index)
        d = {"n": n.name, "k": n.kind or "", "c": n.clean, "d": n.dirty}
        if n.count > 1 and n.mapping is None:
            d["cnt"] = n.count
        if n.full_path is not None:
            d["f"] = n.full_path
        if n.proc is not None:
            d["p"] = proc_index[id(n.proc)]
        if n.mapping is not None:
            m = n.mapping
            i = map_index.get(id(m))
            if i is None:
                i = map_index[id(m)] = len(maps)
                maps.append([m.reason, m.range, [[k, m.fields[k]] for k in TOOLTIP_FIELDS if k in m.fields]])
            d["m"] = i
        if n.sym is not None:
            d["s"] = sym_index[id(n.sym)]
        if n.run is not None:
            d["r"] = ["%x" % n.run[0], "%x" % n.run[1]]
        if n.children:
            d["ch"] = [conv(c) for c in n.children]
        return d

    return conv(root), node_index


def mapping_rows(procs, proc_index, node_index, metric):
    """Every mapping shown in the flame graph: [proc, group, node, Size, Referenced, Rss, Pss,
    Private_Clean, Private_Dirty, Shared_Clean + Shared_Dirty] (the "referenced" metric: referenced and
    not referenced kB instead of Private_Clean and Private_Dirty); group indexes the returned list of
    group names."""
    groups, group_index, rows = [], {}, []
    for p in procs:
        for m in p.maps:
            if m.node is None:
                continue
            g = " \u203a ".join(m.path)
            gi = group_index.get(g)
            if gi is None:
                gi = group_index[g] = len(groups)
                groups.append(g)
            f = m.fields
            a, b = (m.ref, m.unref) if metric == "referenced" else (m.clean, m.dirty)
            rows.append([proc_index[id(p)], gi, node_index[id(m.node)], f.get("Size", 0), f.get("Referenced", 0),
                         m.rss, m.pss, a, b, m.shared])
    return groups, rows


class JsonContext:
    """Indexes shared by the views of one HTML page."""
    def __init__(self, procs):
        self.proc_index = {id(p): i for i, p in enumerate(procs)}
        self.sym_index = {id(s): i for i, s in enumerate(s for p in procs for s in p.symbols)}
        self.maps, self.map_index = [], {}


def view_json(root, procs, jc, metric):
    """The data of one flame graph view, taken right after its tree is built (m.path, m.node and the
    symbol nodes belong to that tree)."""
    tree, node_index = tree_json(root, jc.proc_index, jc.sym_index, jc.maps, jc.map_index)
    group_names, mapping_list = mapping_rows(procs, jc.proc_index, node_index, metric)
    root_index = node_index[id(root)]
    shown = [m for p in procs for m in p.maps if m.node is not None]
    return {
        "metric": metric,
        "count": len(shown),
        "unknown": sum(1 for m in shown if m.runs is None) if metric == "referenced" else 0,
        "tree": tree,
        "groupNames": group_names,
        "mappings": mapping_list,
        "symNodes": [[[node_index[id(n)] for n in s.nodes], node_index[id(s.home)] if s.home is not None else root_index]
                     for p in procs for s in p.symbols],
    }


def write_html(views, layout, metric, jc, procs, single, source, segments, out):
    symbols = [[jc.proc_index[id(p)], s.name, basename(s.elf), s.elf, s.section, s.typ, "%x" % s.addr, s.size,
                s.pages, round(s.referenced, 4), s.clean, s.dirty]
               for p in procs for s in p.symbols]
    total_maps = sum(p.count for p in procs)
    data = {
        "title": ("Memory flame graph \u2013 %s" % procs[0].label) if single and len(procs) == 1
                 else "System memory flame graph \u2013 %s" % source,
        "source": source,
        "name": "%s_%s" % (procs[0].prog, procs[0].pid) if single and len(procs) == 1 else "system",
        "single": single,
        "layout": layout,
        "metric": metric,
        "views": views,
        "procs": [[p.pid, p.prog, p.exe, p.count, p.rss, p.pss, p.clean, p.dirty, p.uss, p.cmd, p.shared,
                   list(mallinfo_kb(p.mallinfo)) if p.mallinfo is not None else None, p.hp_private, p.hp_shared,
                   p.thp]
                  for p in procs],
        "symbols": symbols,
        "totalMaps": total_maps,
        # processes whose page types are exact (from /proc/kpageflags)
        "pfnProcs": sum(1 for p in procs if p.maps.kinds is not None and p.maps.pfn),
        # processes whose KSM flags were ignored (kernel bug, see ksm_checker)
        "ksmIgnored": sum(1 for p in procs if p.maps.ksm_ignored),
        "pageSize": PAGE,
        "options": "%ssegments: %s" % ("single process, " if single else "", "on" if segments else "off"),
        "maps": jc.maps,
    }
    payload = json.dumps(data, separators=(",", ":"), ensure_ascii=False).replace("</", "<\\/")
    out.write(HTML_TEMPLATE.replace("__TITLE__", html.escape(data["title"])).replace("__DATA__", payload))


def write_table(out, header, rows, min_widths):
    """";"-separated table with fixed-width columns (widened only for longer values): numbers
    right-aligned, text left-aligned, a trailing text column unpadded. Text containing ";" or '"'
    is quoted as in CSV. None is printed as "-"."""
    def cell(v):
        if v is None:
            return "-"
        s = str(v)
        if isinstance(v, float):
            return "%.2f" % v
        return '"%s"' % s.replace('"', '""') if ";" in s or '"' in s else s
    cells = [[cell(v) for v in r] for r in rows]
    numeric = [all(r[i] is None or isinstance(r[i], (int, float)) for r in rows) for i in range(len(header))]
    widths = [max([len(h), w] + [len(r[i]) for r in cells]) for i, (h, w) in enumerate(zip(header, min_widths))]

    def line(vals):
        last = len(vals) - 1
        return ";".join(v.rjust(widths[i]) if numeric[i] else v if i == last else v.ljust(widths[i])
                        for i, v in enumerate(vals)) + "\n"
    out.write(line(header))
    for r in cells:
        out.write(line(r))


def process_table(procs, before=None):
    """(header, rows, min widths) of the process table: one row per process sorted by USS, values in kB;
    # MAPPINGS: all mappings of the process, PRIVATE HP / SHARED HP: hugetlb pages (Private_Hugetlb /
    Shared_Hugetlb, not included in USS, RSS, PSS, SHARED), THP: transparent huge pages (AnonHugePages +
    ShmemPmdMapped + FilePmdMapped, included in RSS).
    before: {pid: USS} of an earlier sample, adds USS DIFF (USS - earlier USS)."""
    procs = sorted(procs, key=lambda p: -p.uss)
    header = ["PID", "COMMAND", "USS", "SHARED", "RSS", "PSS", "# MAPPINGS", "PRIVATE HP", "SHARED HP", "THP"]
    widths = [7, 15, 6, 6, 6, 6, 10, 6, 6, 6]
    with_mallinfo = any(p.mallinfo is not None for p in procs)
    if with_mallinfo:
        header, widths = header + ["SYSTEM", "ALLOC", "FREE", "ALLOC/SYSTEM %"], widths + [6, 6, 6, 14]
    if before is not None:
        header, widths = header + ["USS DIFF"], widths + [10]

    def proc_row(p):
        r = [p.pid, p.cmd, p.uss, p.shared, p.rss, p.pss, p.count, p.hp_private, p.hp_shared, p.thp]
        if with_mallinfo:
            if p.mallinfo is None:
                r += [None] * 4
            else:
                system, alloc, free = mallinfo_kb(p.mallinfo)
                r += [system, alloc, free, 100.0 * alloc / system if system else None]
        if before is not None:
            r.append(p.uss - before[p.pid] if p.pid in before else None)
        return r
    return header, [proc_row(p) for p in procs], widths


def print_summary(procs, out, before=None):
    """One row per process sorted by USS (values in kB).
    before: the processes of an earlier sample, adds the USS change."""
    before_uss = {p.pid: p.uss for p in before} if before is not None else None
    write_table(out, *process_table(procs, before_uss))
    if before is not None:
        common = [p for p in procs if p.pid in before_uss]
        old, new = sum(before_uss[p.pid] for p in common), sum(p.uss for p in common)
        out.write("total USS of %d process(es): before %d kB, after %d kB, diff %+d kB\n" % (
            len(common), old, new, new - old))


class HelpFormatter(argparse.RawTextHelpFormatter):
    """Lists every option by its first name only, with its argument unless that is an optional list;
    the help texts start at column 24."""
    def __init__(self, prog):
        super().__init__(prog)
        self._action_max_length = self._max_help_position - 2

    def _format_action_invocation(self, action):
        opt = action.option_strings[0]
        if action.nargs == 0 or action.nargs == "*":
            return opt
        return "%s %s" % (opt, self._format_args(action, self._get_default_metavar_for_optional(action)))


def main():
    ap = argparse.ArgumentParser(
        description="Print the memory summary (USS = Private_Clean + Private_Dirty) from /proc/<pid>/smaps\n"
                    "of a process or the whole system, optionally with a flame graph.",
        epilog=__doc__[__doc__.index("examples:"):], formatter_class=HelpFormatter)
    src = ap.add_mutually_exclusive_group()
    src.add_argument("-p", "--pid", type=int, metavar="PID", help="process ID to analyze")
    src.add_argument("-s", "--system", action="store_true", help="analyze all processes of the system")
    src.add_argument("-i", "--input", metavar="FILE",
                     help="process a raw smaps file or output from\n`tail -n +1 /proc/*/smaps`")
    ap.add_argument("-d", "--dump", nargs="?", const="", metavar="FILE",
                    help="with -p / -s: also save the raw smaps to FILE")
    ap.add_argument("-f", "--flame", action="store_true",
                    help="write the flame graph as an interactive HTML page")
    ap.add_argument("-g", "--globals", dest="symbols", nargs="*", metavar="ELF",
                    help="with -p -f: show the global variables of the main executable")
    ap.add_argument("--all-symbols", action="store_true",
                    help="with -g: include every sized symbol (functions too)")
    ap.add_argument("-m", "--mallinfo", nargs="*", type=int, metavar="PID",
                    help="with -p / -s: attach gdb to the given processes\n"
                         "and calls glibc mallinfo() in the output we have\n"
                         "SYSTEM (arena + hblkhd),\n"
                         "ALLOC (uordblks + usmblks + hblkhd)\n"
                         "FREE (fordblks + fsmblks)\n"
                         "each process is stopped while gdb is attached\n"
                         "if the process was inside malloc we can have a deadlock")
    ap.add_argument("-t", "--trim", nargs="*", type=int, metavar="PID",
                    help="with -p / -s: collect the process statistics (BEFORE),\n"
                         "call malloc_trim(0) by gdb, then collect new statistics (AFTER)")
    if len(sys.argv) == 1:
        ap.print_help()
        sys.exit(0)
    args = ap.parse_args()
    if not (args.pid or args.system or args.input):
        ap.error("one of -p, -s or -i is required")
    if args.dump is not None and args.input:
        ap.error("-d can only be used with -p or -s")
    if args.symbols is not None and not args.pid:
        ap.error("-g can only be used with -p (it needs the running process)")
    if (args.symbols is not None or args.all_symbols) and not args.flame:
        ap.error("-g and --all-symbols can only be used with -f (the symbols are shown in the flame graph)")
    if args.mallinfo is not None:
        if args.input:
            ap.error("-m can only be used with -p or -s (it needs the running process)")
    if args.trim is not None:
        if args.input:
            ap.error("-t can only be used with -p or -s (it needs the running process)")
        if args.mallinfo is None:
            args.mallinfo = args.trim

    if args.trim is None:
        collect(args)
        return
    before = collect(args, phase="before")
    results, failed = gdb_each(before, args.trim or None, "calling malloc_trim(0)", malloc_trim)
    warn_failed("malloc_trim(0)", failed)
    sys.stderr.write("malloc_trim(0) released memory in %d of %d process(es)\n" % (
        sum(1 for r in results.values() if r == 1), len(results)))
    collect(args, pids=[p.pid for p in before], phase="after", before=before)


def collect(args, pids=None, phase=None, before=None):
    """Reads and analyzes the processes, writes the flame graph (with -f) and prints the summary; returns
    the processes. phase: "before" / "after" of -t, added to the file names and the console output;
    before: the processes of the "before" sample."""
    def phased(name):
        if phase is None:
            return name
        root, ext = os.path.splitext(name)
        return "%s_%s%s" % (root, phase, ext)

    tag = "system" if args.system else str(args.pid)
    if args.input:
        by_pid, system = read_file(args.input)
        source = os.path.basename(args.input)
        live = False
        try:
            sample_time = int(os.stat(args.input).st_mtime)
        except OSError:
            sample_time = int(time.time())
    else:
        pids = pids or ([args.pid] if args.pid else all_pids())
        system = len(pids) > 1 or args.system
        dump_name = phased(args.dump or "smaps_dump_%s.txt" % tag)
        dump = open(dump_name, "w", encoding="utf-8") if args.dump is not None else None
        try:
            by_pid, skipped, no_pagemap = read_live(pids, dump)
        finally:
            if dump is not None:
                dump.close()
                sys.stderr.write("wrote raw smaps to %s\n" % dump_name)
        if skipped:
            reasons = {}
            for pid, why in skipped:
                reasons.setdefault(why, []).append(pid)
            for why, lst in reasons.items():
                sys.stderr.write("warning: skipped %d process(es) (%s)%s\n" % (
                    len(lst), why, ": " + " ".join(map(str, lst[:20])) + (" ..." if len(lst) > 20 else "")))
            if any(why == "permission denied" for _, why in skipped) and os.geteuid() != 0:
                sys.stderr.write("         run as root to include processes of other users\n")
        if no_pagemap:
            sys.stderr.write("warning: cannot read /proc/<pid>/pagemap of %d process(es)%s; their referenced "
                             "pages are estimated from Rss + Swap\n" % (
                                 len(no_pagemap), ": " + " ".join(map(str, no_pagemap[:20])) +
                                 (" ..." if len(no_pagemap) > 20 else "")))
        ksm = [(pid, maps.ksm_ignored) for pid, maps in by_pid.items() if maps.ksm_ignored]
        if ksm:
            sys.stderr.write(
                "warning: /proc/kpageflags flags more pages as KSM than /proc/<pid>/ksm_merging_pages has "
                "merged in %d process(es) (%s); the KSM page type is ignored for them - kernel bug flagging "
                "every anonymous page as KSM (Linux 6.10 - 7.2-rc2, fixed by 81401cebfc15)\n" % (
                    len(ksm), ", ".join("%s: %d flagged, %d merged" % (pid, f, m) for pid, (f, m) in ksm[:5]) +
                    (" ..." if len(ksm) > 5 else "")))
        source = os.uname().nodename + (" (system)" if args.system else "")
        live = True
        sample_time = int(time.time())

    single = not system
    # the HTML page of a system view can switch between both layouts and opens the one built last
    # ("program"), so m.path also reflects it for the console summary
    layouts = ["grouped", "program"] if args.flame and not single else ["program"]
    procs = analyze(by_pid, layouts, live)
    if not procs:
        sys.exit("no mappings found")
    if args.symbols is not None:
        def warn(msg):
            sys.stderr.write("warning: %s\n" % msg)
        for p in procs:
            read_symbols(p, args.symbols, args.all_symbols, SYMBOL_MIN_SIZE, warn)
    if args.mallinfo is not None:
        collect_mallinfo(procs, args.mallinfo or None)

    out_name = None
    if args.flame:
        out_name = write_flame(args, procs, layouts, single, source, sample_time, tag, phased)
    if phase is not None:
        sys.stdout.write("%s%s\n" % ("\n" if phase == "after" else "",
                                     "AFTER malloc_trim(0):" if phase == "after" else "BEFORE malloc_trim(0):"))
    print_summary(procs, sys.stdout, before)
    sys.stdout.flush()
    if out_name is not None:
        sys.stderr.write("wrote %s\n" % out_name)
    return procs


def write_flame(args, procs, layouts, single, source, sample_time, tag, phased):
    """Builds every view of the flame graph, the USS one last as it opens first, and writes the HTML
    page; returns its file name."""
    segments = single
    jc = JsonContext(procs)
    views = OrderedDict()
    metrics = ["referenced", "uss"]
    for metric in metrics:
        for layout in layouts:
            use_layout(procs, layout)
            root = build_tree(procs, single, layout, segments, metric)
            if args.symbols is not None:
                for p in procs:
                    (attach_symbols if metric == "uss" else home_symbols)(p)
            finalize(root)
            views["%s:%s" % (metric, layout)] = view_json(root, procs, jc, metric)

    if single:
        tag = "%s_%s" % (re.sub(r"[^\w.+-]", "_", procs[0].prog), procs[0].pid)
    elif args.input:
        tag = os.path.basename(args.input).split(".")[0]
    stamp = time.strftime("%Y%m%d_%H%M%S", time.localtime(sample_time))
    out_name = phased("flame_%s_%s.html" % (tag, stamp))
    with open(out_name, "w", encoding="utf-8") as out:
        write_html(views, layouts[-1], metrics[-1], jc, procs, single, source, segments, out)
    return out_name


HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>__TITLE__</title>
<style>
  :root { --bg:#fafafa; --fg:#222; --muted:#666; --border:#ddd; --accent:#c0392b; }
  * { box-sizing: border-box; }
  body { margin:0; font-family: -apple-system, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; background:var(--bg); color:var(--fg); }
  header { padding:12px 20px; background:#fff; border-bottom:1px solid var(--border); display:flex; flex-wrap:wrap; gap:14px; align-items:center; }
  header h1 { font-size:18px; margin:0 12px 0 0; }
  .controls { display:flex; flex-wrap:wrap; gap:12px; align-items:center; font-size:13px; }
  .controls input[type=text] { padding:4px 8px; border:1px solid #bbb; border-radius:4px; width:200px; }
  .opts { font-size:12px; color:var(--muted); }
  button { padding:4px 10px; border:1px solid #bbb; background:#fff; border-radius:4px; cursor:pointer; font-size:13px; }
  button:hover { background:#f0f0f0; }
  main { padding:12px 20px; }
  #summary { font-size:13px; color:var(--muted); margin-bottom:8px; min-height:18px; }
  #summary b { color:var(--fg); }
  #breadcrumb { font-size:12px; margin-bottom:6px; min-height:16px; }
  #breadcrumb span { cursor:pointer; color:#2a6ebb; }
  #breadcrumb span:hover { text-decoration:underline; }
  #chartWrap { position:relative; background:#fff; border:1px solid var(--border); border-radius:4px; }
  canvas { display:block; width:100%; cursor:pointer; }
  #tooltip { position:fixed; pointer-events:none; background:rgba(30,30,30,.95); color:#fff; font-size:12px; padding:8px 10px; border-radius:4px; max-width:560px; display:none; z-index:10; line-height:1.45; }
  #tooltip .t { font-weight:bold; word-break:break-all; margin-bottom:4px; }
  #tooltip td { padding:0 8px 0 0; }
  #tooltip td:last-child { text-align:right; font-family:monospace; }
  h2 { font-size:15px; margin:22px 0 8px; }
  table.list { border-collapse:collapse; font-size:12px; background:#fff; width:100%; }
  table.list th, table.list td { border:1px solid var(--border); padding:3px 8px; }
  table.list th { background:#f3f3f3; cursor:pointer; user-select:none; text-align:left; }
  table.list td.n { text-align:right; font-family:monospace; }
  table.list tr:hover td { background:#fff8e6; }
  table.list tbody tr { cursor:pointer; }
  table.list tr.sel td { background:#ffe9a8; font-weight:bold; }
  h2 button.csv { margin-left:10px; font-size:12px; font-weight:normal; padding:2px 8px; vertical-align:2px; }
  .hint { font-size:12px; color:var(--muted); margin-top:14px; }
  .legend { display:flex; gap:12px; font-size:12px; color:var(--muted); }
  .legend i { display:inline-block; width:12px; height:12px; border-radius:2px; vertical-align:-2px; margin-right:4px; }
</style>
</head>
<body>
<header>
  <h1 id="heading">smaps &rarr; USS Flame Graph</h1>
  <div class="controls">
    <label>View:
      <select id="optView">
        <option value="uss">USS</option>
        <option value="referenced">Referenced pages</option>
      </select>
    </label>
    <label id="layoutWrap" style="display:none">System view:
      <select id="optLayout">
        <option value="program">Program</option>
        <option value="grouped">Grouped</option>
      </select>
    </label>
    <input type="text" id="search" placeholder="Search (regex)…">
    <button id="reset">Reset zoom</button>
    <label title="width of the blocks of the flame graph">Widths <select id="widths"><option value="size">by size</option><option value="log">log of size (all blocks visible)</option></select></label>
    <label>Unit <select id="unit"><option>kB</option><option>MB</option><option>GB</option></select></label>
    <span class="opts" id="opts"></span>
  </div>
  <div class="legend">
    <span><i style="background:hsl(200,22%,74%)"></i>process</span>
    <span><i style="background:hsl(48,85%,62%)"></i>dynamic allocator</span>
    <span><i style="background:hsl(115,45%,58%)"></i>thread stack</span>
    <span><i style="background:hsl(25,85%,63%)"></i>executable</span>
    <span><i style="background:hsl(210,65%,65%)"></i>anonymous</span>
    <span><i style="background:hsl(268,45%,74%)"></i>file backed</span>
    <span id="symLegend" style="display:none"><i style="background:hsl(175,60%,54%)"></i>variable (symbol)</span>
    <span class="refLegend"><i style="background:hsl(120,40%,62%)"></i>referenced pages</span>
    <span class="refLegend"><i style="background:hsl(0,0%,86%)"></i>not referenced</span>
    <span class="refLegend"><i style="background:hsl(50,30%,84%)"></i>address block</span>
    <span class="refLegend" title="page type of the referenced pages: exact from /proc/kpageflags (root), otherwise estimated from smaps (AnonHugePages, Locked, KernelPageSize); swapped out pages are always exact">page type:
      <i style="background:hsl(120,35%,72%);margin-left:4px"></i>4K
      <i style="background:hsl(165,60%,42%);margin-left:6px"></i>THP
      <i style="background:hsl(195,70%,38%);margin-left:6px"></i>huge
      <i style="background:hsl(0,70%,62%);margin-left:6px"></i>locked
      <i style="background:hsl(285,45%,62%);margin-left:6px"></i>KSM
      <i style="background:hsl(30,45%,48%);margin-left:6px"></i>slab
      <i style="background:hsl(60,45%,80%);margin-left:6px"></i>zero
      <i style="background:hsl(35,95%,58%);margin-left:6px"></i>swapped</span>
    <span><i style="background:#e040fb"></i>search match</span>
    <span><i style="background:#263238"></i>selected in table</span>
  </div>
</header>
<main>
  <div id="summary"></div>
  <div id="breadcrumb"></div>
  <div id="chartWrap"><canvas id="chart"></canvas></div>
  <div id="tableWrap"></div>
</main>
<div id="tooltip"></div>

<script id="data" type="application/json">__DATA__</script>
<script>
"use strict";

const DATA = JSON.parse(document.getElementById("data").textContent);
const ROW_H = 20;
const FONT = "12px Menlo, Consolas, monospace";
const $ = id => document.getElementById(id);
const canvas = $("chart");
const ctx = canvas.getContext("2d");
const tooltip = $("tooltip");
const esc = s => String(s).replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));

// mi: [SYSTEM, ALLOC, FREE] kB from mallinfo() (flame.py -m), null if not collected
// hpPrivate / hpShared: kB of hugetlb pages of the whole process (not in rss, pss, uss, shared);
// thp: kB of transparent huge pages of the whole process (part of rss)
const procs = DATA.procs.map(([pid, prog, exe, count, rss, pss, clean, dirty, uss, cmd, shared, mi, hpPrivate, hpShared, thp], idx) =>
  ({ idx, pid, prog, exe, count, rss, pss, clean, dirty, uss, cmd, shared, mi, hpPrivate, hpShared, thp, label: `${prog}[${pid}]` }));
const withMallinfo = procs.some(p => p.mi);

// nodes of the current view in pre-order (the order flame.py numbered them in); a node's subtree is nodes[pre, end)
// "referenced" view: clean = referenced kB, dirty = not referenced kB
let curView = null, nodes = [], root = null;
let curMetric = DATA.metric, curLayout = DATA.layout;
const isRef = () => curMetric === "referenced";
function hydrate(j, parent) {
  const n = { name: j.n, kind: j.k, parent, clean: j.c, dirty: j.d, value: j.c + j.d, count: j.cnt || 1,
              fullPath: j.f, proc: j.p !== undefined ? procs[j.p] : null,
              mapping: j.m !== undefined ? DATA.maps[j.m] : null, sym: j.s !== undefined ? DATA.symbols[j.s] : null,
              run: j.r || null, children: [], pre: nodes.length };
  nodes.push(n);
  n.depth = parent ? parent.depth + 1 : 0;
  if (j.ch) n.children = j.ch.map(c => hydrate(c, n));
  n.end = nodes.length;
  n.maxDepth = n.children.reduce((d, c) => Math.max(d, 1 + c.maxDepth), 0);
  n.logW = n.children.reduce((s, c) => s + c.logW, 0);
  const own = n.value - n.children.reduce((s, c) => s + c.value, 0);
  if (own > 0 || !n.logW) n.logW += 1 + Math.log2(1 + Math.max(own, 0));
  return n;
}
let focus = null, rects = [], searchRe = null, hoverNode = null;
let selected = null, selectedRow = null, tableFocus = null;   // set by clicking a table row

function loadView() {
  curView = DATA.views[`${curMetric}:${curLayout}`];
  if (!curView.root) {
    nodes = [];
    curView.root = hydrate(curView.tree, null);
    curView.nodes = nodes;
  }
  nodes = curView.nodes;
  root = focus = curView.root;
  hoverNode = selected = selectedRow = tableFocus = null;
}

function zoom(n) {
  focus = n;
  selected = selectedRow = tableFocus = null;
  render();
}
const sortState = { procs: { key: "uss", dir: -1 }, groups: { key: "uss", dir: -1 }, symbols: { key: "uss", dir: -1 } };

/* ---------- rendering ---------- */

function hashStr(s) {
  let h = 0;
  for (let i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) | 0;
  return Math.abs(h);
}

function colorFor(n) {
  const v = hashStr(n.name) % 1000 / 1000;
  switch (n.kind) {
    case "root": return "hsl(0,0%,78%)";
    case "proc": return `hsl(${190 + v * 25},22%,${68 + v * 10}%)`;
    case "alloc": return `hsl(${42 + v * 14},85%,${56 + v * 12}%)`;
    case "stack": return `hsl(${95 + v * 40},45%,${52 + v * 12}%)`;
    case "exec": return `hsl(${14 + v * 22},85%,${58 + v * 10}%)`;
    case "anon": return `hsl(${200 + v * 25},65%,${60 + v * 10}%)`;
    case "file": return `hsl(${255 + v * 25},45%,${70 + v * 8}%)`;
    case "sym": return `hsl(${165 + v * 20},60%,${48 + v * 12}%)`;
    case "ref": return "hsl(120,40%,62%)";
    case "unref": return "hsl(0,0%,86%)";
    case "pk_4k": return "hsl(120,35%,72%)";
    case "pk_thp": return "hsl(165,60%,42%)";
    case "pk_huge": return "hsl(195,70%,38%)";
    case "pk_locked": return "hsl(0,70%,62%)";
    case "pk_ksm": return "hsl(285,45%,62%)";
    case "pk_slab": return "hsl(30,45%,48%)";
    case "pk_zero": return "hsl(60,45%,80%)";
    case "pk_swap": return "hsl(35,95%,58%)";
    case "block": return `hsl(${45 + v * 10},30%,${80 + v * 8}%)`;
  }
  return "#ccc";
}

function matches(n) {
  if (!searchRe) return false;
  return searchRe.test(n.name) || (n.fullPath && searchRe.test(n.fullPath)) || (n.proc && searchRe.test(n.proc.label));
}

function render() {
  const width = canvas.parentElement.clientWidth;
  const levels = focus.depth + focus.maxDepth + 1;
  const height = levels * ROW_H + 4;
  const dpr = window.devicePixelRatio || 1;
  canvas.width = width * dpr;
  canvas.height = height * dpr;
  canvas.style.height = height + "px";
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, width, height);
  ctx.font = FONT;
  ctx.textBaseline = "middle";

  const yOf = d => height - (d + 1) * ROW_H - 2;
  rects = [];
  for (let a = focus.parent; a; a = a.parent) drawRect(a, 0, width, yOf(a.depth), true);

  // log: every leaf gets 1 + log2(1 + kB), a parent the sum of its children (and of its own kB)
  const wOf = widths === "log" ? n => n.logW : n => n.value;
  const scale = wOf(focus) > 0 ? width / wOf(focus) : 0;
  (function walk(n, x) {
    const w = wOf(n) * scale;
    if (w < 0.3) return;
    drawRect(n, x, w, yOf(n.depth), false);
    let cx = x;
    for (const c of n.children) { walk(c, cx); cx += wOf(c) * scale; }
  })(focus, 0);

  updateBreadcrumb();
  updateSummary();
  if (focus !== tableFocus) { tableFocus = focus; renderTables(); }
}

function drawRect(n, x, w, y, ancestor) {
  const sel = selected && selected.has(n);
  ctx.fillStyle = matches(n) ? "#e040fb" : sel ? "#263238" : colorFor(n);
  ctx.globalAlpha = ancestor ? 0.55 : 1;
  ctx.fillRect(x, y, Math.max(w - 1, 0.5), ROW_H - 1);
  ctx.globalAlpha = 1;
  if (n === hoverNode) {
    ctx.strokeStyle = "#000"; ctx.lineWidth = 1.5;
    ctx.strokeRect(x + 0.75, y + 0.75, Math.max(w - 2.5, 0), ROW_H - 2.5);
  }
  if (w > 28) {
    ctx.fillStyle = sel ? "#fff" : "#111";
    const label = isRef() && n.kind !== "ref" && n.kind !== "unref" && !n.kind.startsWith("pk_")
      ? `${n.name} (${fmtKB(n.value)}, ${pct(n.clean, n.value)} referenced)` : `${n.name} (${fmtKB(n.value)})`;
    ctx.fillText(fitText(label, w - 8), x + 4, y + ROW_H / 2);
  }
  rects.push({ n, x, y, w });
}

function fitText(s, maxW) {
  if (ctx.measureText(s).width <= maxW) return s;
  const n = Math.floor(maxW / ctx.measureText("m").width) - 1;
  return n <= 0 ? "" : s.slice(0, n) + "…";
}

let unit = "kB", widths = "size";
function fmtKB(kb) {
  if (unit === "GB") return (kb / 1048576).toFixed(3) + " GB";
  if (unit === "MB") return (kb / 1024).toFixed(2) + " MB";
  return kb + " kB";
}

function pct(a, b) { return b > 0 ? (100 * a / b).toFixed(2) + "%" : "-"; }

function updateBreadcrumb() {
  const chain = [];
  for (let n = focus; n; n = n.parent) chain.unshift(n);
  const bc = $("breadcrumb");
  bc.innerHTML = "";
  chain.forEach((n, i) => {
    if (i) bc.append(" › ");
    const s = document.createElement("span");
    s.textContent = n.name;
    s.onclick = () => zoom(n);
    bc.append(s);
  });
}

function updateSummary() {
  const one = DATA.single && procs.length === 1 ? procs[0] : null;
  const who = one ? `<b>${esc(one.label)}</b>` : `${procs.length} processes`;
  let txt = isRef()
    ? `Total size: <b>${fmtKB(root.value)}</b>, referenced: <b>${fmtKB(root.clean)}</b> (${pct(root.clean, root.value)})` +
      ` &nbsp; · &nbsp; ${who}, ${DATA.totalMaps} mappings, ${curView.count} without ---p reservations` +
      (curView.unknown ? `, ${curView.unknown} of them without pagemap data (referenced pages estimated from Rss + Swap)` : "") +
      ` &nbsp; · &nbsp; page types: ` + (DATA.pfnProcs === procs.length ? "exact (/proc/kpageflags)"
        : DATA.pfnProcs ? `exact for ${DATA.pfnProcs} of ${procs.length} processes, otherwise estimated from smaps`
        : "estimated from smaps, swapped out pages exact (run as root for exact page types)") +
      (DATA.ksmIgnored ? `, KSM flag ignored for ${DATA.ksmIgnored} process(es): the kernel flags every anonymous ` +
        `page as KSM (bug of Linux 6.10 - 7.2-rc2), more than /proc/&lt;pid&gt;/ksm_merging_pages` : "")
    : `Total USS: <b>${fmtKB(root.value)}</b> &nbsp; · &nbsp; ${who}, ${DATA.totalMaps} mappings, ${curView.count} with USS &gt; 0`;
  if (searchRe) {
    // sum of the topmost matching nodes, so nested matches are not counted twice
    let total = 0, count = 0;
    (function walk(n) {
      if (matches(n)) { total += n.value; count++; return; }
      n.children.forEach(walk);
    })(root);
    txt += ` &nbsp; · &nbsp; Matched: <b>${fmtKB(total)}</b> (${pct(total, root.value)}) in ${count} nodes`;
  }
  $("summary").innerHTML = txt;
}

/* ---------- interaction ---------- */

function hitTest(ev) {
  const r = canvas.getBoundingClientRect();
  const x = ev.clientX - r.left, y = ev.clientY - r.top;
  for (let i = rects.length - 1; i >= 0; i--) {
    const q = rects[i];
    if (x >= q.x && x < q.x + q.w && y >= q.y && y < q.y + ROW_H) return q.n;
  }
  return null;
}

canvas.addEventListener("mousemove", ev => {
  const n = hitTest(ev);
  if (n !== hoverNode) { hoverNode = n; render(); }
  if (!n) { tooltip.style.display = "none"; return; }
  showTooltip(n, ev);
});
canvas.addEventListener("mouseleave", () => { hoverNode = null; tooltip.style.display = "none"; render(); });
canvas.addEventListener("click", ev => {
  const n = hitTest(ev);
  if (n) zoom(n);
});

function showTooltip(n, ev) {
  const rows = isRef()
    ? [["Size", fmtKB(n.value)], ["Referenced", `${fmtKB(n.clean)} (${pct(n.clean, n.value)})`], ["Not referenced", fmtKB(n.dirty)]]
    : [["USS", fmtKB(n.value)]];
  rows.push(["% of total", pct(n.value, root.value)]);
  if (n.parent) rows.push(["% of parent", pct(n.value, n.parent.value)]);
  if (!n.mapping && n.count > 1) rows.push(["mappings", n.count]);
  if (n.run) rows.push(["Range", `${n.run[0]}-${n.run[1]}`], ["Pages", Math.round(n.value * 1024 / DATA.pageSize)]);
  let title = esc(n.name);
  if (n.fullPath !== undefined && n.fullPath !== n.name) title += `<div style="font-weight:normal;color:#ccc">${esc(n.fullPath || "[anon]")}</div>`;
  const p = n.proc;
  if (p) {
    rows.push(["—", ""]);
    rows.push(["PID", p.pid], ["Program", p.prog], ["Process USS", fmtKB(p.uss)], ["Process Rss", fmtKB(p.rss)], ["Process Pss", fmtKB(p.pss)]);
  }
  const m = n.mapping;
  if (m) {
    const [reason, range, fields] = m;
    rows.push(["—", ""]);
    rows.push(["Classified", reason], ["Range", range]);
    for (const [k, v] of fields) rows.push([k, fmtKB(v)]);
  }
  const s = n.sym;
  if (s) {
    const [, , elf, , section, type, addr, size, pages, referenced] = s;
    rows.push(["—", ""]);
    rows.push(["Variable in", `${elf} ${section}`], ["nm type", type], ["Address", addr],
      ["Size", `${size} B (${pages} pages)`], ["Referenced", pct(referenced, 1)]);
  }
  tooltip.innerHTML = `<div class="t">${title}</div><table>${
    rows.map(([k, v]) => k === "—" ? `<tr><td colspan=2><hr style="border:0;border-top:1px solid #555;margin:3px 0"></td></tr>` : `<tr><td>${esc(k)}</td><td>${esc(v)}</td></tr>`).join("")
  }</table>`;
  tooltip.style.display = "block";
  const pad = 14;
  let x = ev.clientX + pad, y = ev.clientY + pad;
  const tw = tooltip.offsetWidth, th = tooltip.offsetHeight;
  if (x + tw > window.innerWidth) x = ev.clientX - tw - pad;
  if (y + th > window.innerHeight) y = ev.clientY - th - pad;
  tooltip.style.left = Math.max(0, x) + "px";
  tooltip.style.top = Math.max(0, y) + "px";
}

$("reset").addEventListener("click", () => zoom(root));
$("unit").addEventListener("change", ev => {
  unit = ev.target.value;
  render();
  renderTables();
});
$("widths").addEventListener("change", ev => { widths = ev.target.value; render(); });
$("widths").value = widths;
$("search").addEventListener("input", ev => {
  const v = ev.target.value.trim();
  try { searchRe = v ? new RegExp(v, "i") : null; ev.target.style.borderColor = ""; }
  catch (e) { searchRe = null; ev.target.style.borderColor = "red"; }
  render();
});
window.addEventListener("resize", render);
document.addEventListener("keydown", ev => {
  if (ev.key === "Escape") zoom(root);
});

/* ---------- tables ---------- */

const tableRows = {}, tableCols = {};

// ";"-separated like the console output; sizes in kB, percentages without the "%" sign
function exportCSV(id) {
  const cols = tableCols[id];
  const cell = v => /[;"\n]/.test(String(v)) ? `"${String(v).replace(/"/g, '""')}"` : String(v);
  const lines = [cols.map(([, t, fmt]) => cell(fmt === "%" ? t + " [%]" : fmt ? t + " [kB]" : t)).join(";")];
  for (const r of tableRows[id]) {
    lines.push(cols.map(([k, , fmt]) => cell(r[k] === null ? "-" : fmt === "%" ? (100 * r[k]).toFixed(2) : r[k])).join(";"));
  }
  const view = [];
  for (let n = focus; n && n.parent; n = n.parent) view.unshift(n.name);
  const name = ["memflame", DATA.name, curMetric, ...view, id].join("_").replace(/[^\w.+-]+/g, "_").replace(/_+/g, "_");
  const a = document.createElement("a");
  // the BOM makes Excel read the file as UTF-8 instead of the ANSI code page ("›" in group names)
  a.href = URL.createObjectURL(new Blob(["\uFEFF" + lines.join("\n") + "\n"], { type: "text/csv;charset=utf-8" }));
  a.download = name + ".csv";
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
}

function tableHTML(id, title, cols, rows) {
  const { key, dir } = sortState[id];
  rows.sort((a, b) => (typeof a[key] === "string" ? a[key].localeCompare(b[key]) : a[key] - b[key]) * dir);
  tableRows[id] = rows;
  tableCols[id] = cols;
  const arrow = k => k === key ? (dir > 0 ? " ▲" : " ▼") : "";
  let html = `<h2>${title} <button class="csv" data-csv="${id}">Export CSV</button></h2>` +
    `<table class="list" data-table="${id}"><thead><tr>${
    cols.map(([k, t]) => `<th data-k="${k}">${t}${arrow(k)}</th>`).join("")
  }</tr></thead><tbody>`;
  rows.forEach((r, i) => {
    html += `<tr data-i="${i}"${selectedRow === id + "\0" + r.key ? ' class="sel"' : ""}>` +
      cols.map(([k, , fmt]) => r[k] === null ? `<td class="n">-</td>` :
        fmt === "%" ? `<td class="n">${pct(r[k], 1)}</td>` :
        fmt ? `<td class="n">${fmtKB(r[k])}</td>` :
        typeof r[k] === "number" ? `<td class="n">${r[k]}</td>` : `<td>${esc(r[k])}</td>`).join("") +
      `</tr>`;
  });
  return html + "</tbody></table>";
}

function lca(a, b) {
  while (a.depth > b.depth) a = a.parent;
  while (b.depth > a.depth) b = b.parent;
  while (a !== b) { a = a.parent; b = b.parent; }
  return a;
}

// zoom to the smallest flame graph node holding all mappings of the row and highlight their nodes
function selectRow(id, row) {
  let target = null;
  for (const n of row.nodes) target = target ? lca(target, n) : n;
  focus = tableFocus = target;
  selected = row.nodes;
  selectedRow = id + "\0" + row.key;
  render();
  renderTables();
  window.scrollTo({ top: 0, behavior: "smooth" });
}

// aggregates the mappings below the current flame graph node
function viewRows() {
  const byProc = new Map(), byGroup = new Map();
  for (const [pi, gi, ni, size, referenced, rss, pss, clean, dirty, shared] of curView.mappings) {
    if (ni < focus.pre || ni >= focus.end) continue;
    const node = nodes[ni], uss = clean + dirty;
    let p = byProc.get(pi);
    if (!p) {
      const proc = procs[pi], [miSystem, miAlloc, miFree] = proc.mi || [null, null, null];
      const miRatio = miSystem ? miAlloc / miSystem : null;
      byProc.set(pi, p = { key: pi, pid: proc.pid, prog: proc.prog, cmd: proc.cmd, count: 0, rss: 0, pss: 0, shared: 0,
                           clean: 0, dirty: 0, uss: 0, hpPrivate: proc.hpPrivate, hpShared: proc.hpShared, thp: proc.thp,
                           miSystem, miAlloc, miFree, miRatio, nodes: new Set() });
    }
    p.count++; p.rss += rss; p.pss += pss; p.shared += shared; p.clean += clean; p.dirty += dirty; p.uss += uss; p.nodes.add(node);
    let g = byGroup.get(gi);
    if (!g) byGroup.set(gi, g = { key: gi, name: curView.groupNames[gi], procSet: new Set(), count: 0, size: 0, referenced: 0, clean: 0, uss: 0, nodes: new Set() });
    g.procSet.add(pi); g.count++; g.size += size; g.referenced += referenced; g.clean += clean; g.uss += uss; g.nodes.add(node);
  }
  for (const g of byGroup.values()) {
    g.procs = g.procSet.size;
    g.refShare = g.size > 0 ? g.referenced / g.size : 0;
  }
  // "referenced" view: share of the size on referenced pages
  for (const r of [...byProc.values(), ...byGroup.values()]) r.refPct = r.uss > 0 ? r.clean / r.uss : 0;
  // symbols: those with private pages in the view, and those without any whose mapping is in the view
  const inView = ni => ni >= focus.pre && ni < focus.end;
  const symRows = [];
  DATA.symbols.forEach(([pi, name, elf, elfPath, section, type, addr, size, pages, referenced, clean, dirty], i) => {
    const [own, home] = curView.symNodes[i];
    if (own.length ? !own.some(inView) : !inView(home)) return;
    const r = { key: i, pid: procs[pi].pid, name, elf, section, type, addr, size, referenced, uss: clean + dirty,
                nodes: new Set((own.length ? own : [home]).map(ni => nodes[ni])) };
    if (isRef()) {
      // the pages owned by the variable in this view and the referenced ones of them
      r.uss = r.clean = 0;
      for (const ni of own) { r.uss += nodes[ni].value; r.clean += nodes[ni].clean; }
      r.refPct = r.uss > 0 ? r.clean / r.uss : 0;
    }
    symRows.push(r);
  });
  for (const r of [...byProc.values(), ...byGroup.values(), ...symRows]) r.share = focus.value > 0 ? r.uss / focus.value : 0;
  return { procRows: [...byProc.values()], groupRows: [...byGroup.values()], symRows };
}

function renderTables() {
  const one = DATA.single && procs.length === 1 ? procs[0] : null;
  const view = [];
  for (let n = focus; n && n.parent; n = n.parent) view.unshift(n.name);
  const where = esc(view.length ? view.join(" › ") : one ? one.label : "all processes");
  const { procRows, groupRows, symRows } = viewRows();
  const ref = isRef();
  const procCols = ref
    ? [["pid", "PID"], ["prog", "Program"], ["count", "# mappings"], ["uss", "Size", 1], ["share", "% of size", "%"],
       ["clean", "Referenced", 1], ["refPct", "% referenced", "%"], ["dirty", "Not referenced", 1]]
    : [["pid", "PID"], ["cmd", "COMMAND"], ["uss", "USS", 1], ["share", "%USS", "%"], ["shared", "SHARED", 1],
       ["rss", "RSS", 1], ["pss", "PSS", 1], ["count", "# MAPPINGS"], ["hpPrivate", "PRIVATE HP", 1],
       ["hpShared", "SHARED HP", 1], ["thp", "THP", 1]].concat(withMallinfo
      ? [["miSystem", "SYSTEM", 1], ["miAlloc", "ALLOC", 1], ["miFree", "FREE", 1], ["miRatio", "ALLOC/SYSTEM %", "%"]] : []);
  const procTable = tableHTML("procs", `${ref ? "Referenced pages" : "USS"} per process – ${where}`, procCols, procRows);
  const groupCols = ref
    ? [["name", "Group"], ["uss", "Size", 1], ["share", "% of size", "%"], ["clean", "Referenced", 1],
       ["refPct", "% referenced", "%"], ["count", "# mappings"]]
    : [["name", "Group"], ["uss", "USS", 1], ["share", "% USS", "%"], ["size", "Size", 1],
       ["refShare", "Referenced", "%"], ["count", "# mappings"]];
  if (!one) groupCols.push(["procs", "# processes"]);
  const groupTable = tableHTML("groups", `${ref ? "Referenced pages" : "USS"} per group – ${where}`, groupCols, groupRows);
  let symTable = "";
  if (DATA.symbols.length) {
    const symCols = ref
      ? [["name", "Variable"], ["uss", "Size of pages", 1], ["share", "% of size", "%"], ["clean", "Referenced", 1],
         ["refPct", "% referenced", "%"], ["size", "Size [B]"], ["section", "Section"], ["type", "nm type"],
         ["addr", "Address"], ["elf", "ELF"]]
      : [["name", "Variable"], ["uss", "USS", 1], ["share", "% USS", "%"],
         ["referenced", "Referenced", "%"], ["size", "Size [B]"], ["section", "Section"], ["type", "nm type"],
         ["addr", "Address"], ["elf", "ELF"]];
    if (!one) symCols.push(["pid", "PID"]);
    symTable = tableHTML("symbols", `Variables – ${where}`, symCols, symRows) + (ref
      ? `<div class="hint">Size of pages: the pages owned by the variable (each page by the variable covering most of it); ` +
        `Referenced: those of them present in RAM or swapped out.</div>`
      : `<div class="hint">USS: private resident pages, each owned by the variable covering most of it. ` +
        `Referenced: share of the variable's pages that are in RAM, i.e. were read or written ` +
        `(a page shared by several variables counts for each).</div>`);
  }
  const hint = ref
    ? `Mappings (without ---p reservations) in the current flame graph view; Size: their address space, ` +
      `Referenced: their pages present in RAM or swapped out (/proc/&lt;pid&gt;/pagemap), i.e. pages that were read or written; ` +
      `click a row to show it in the flame graph.`
    : `Mappings with USS &gt; 0 in the current flame graph view; click a row to show it in the flame graph.`;
  $("tableWrap").innerHTML = `<div class="hint">${hint}</div>` + procTable + groupTable + symTable;

  $("tableWrap").querySelectorAll("table[data-table]").forEach(t => {
    const id = t.dataset.table;
    t.querySelectorAll("th[data-k]").forEach(th => th.onclick = () => {
      const k = th.dataset.k, s = sortState[id];
      sortState[id] = { key: k, dir: s.key === k ? -s.dir : (k === "name" || k === "prog" || k === "cmd" ? 1 : -1) };
      renderTables();
    });
    t.querySelectorAll("tr[data-i]").forEach(tr => tr.onclick = () => selectRow(id, tableRows[id][+tr.dataset.i]));
  });
  $("tableWrap").querySelectorAll("button[data-csv]").forEach(b => b.onclick = () => exportCSV(b.dataset.csv));
}

function updateChrome() {
  $("heading").textContent = `smaps → ${isRef() ? "Referenced Pages" : "USS"} Flame Graph`;
  $("symLegend").style.display = DATA.symbols.length ? "" : "none";
  document.querySelectorAll(".refLegend").forEach(e => e.style.display = isRef() ? "" : "none");
}

$("opts").textContent = `${DATA.source} · ${DATA.options}`;
const layouts = new Set(Object.keys(DATA.views).map(k => k.split(":")[1]));
if (layouts.size > 1) $("layoutWrap").style.display = "";
$("optLayout").value = curLayout;
$("optView").value = curMetric;
$("optLayout").addEventListener("change", ev => {
  curLayout = ev.target.value;
  loadView();
  tooltip.style.display = "none";
  render();
});
$("optView").addEventListener("change", ev => {
  curMetric = ev.target.value;
  loadView();
  updateChrome();
  tooltip.style.display = "none";
  render();
});
loadView();
updateChrome();
render();
</script>
</body>
</html>
"""

if __name__ == "__main__":
    main()
