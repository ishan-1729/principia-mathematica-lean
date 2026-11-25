#!/usr/bin/env python3
"""Type-check individual files with `lake env lean`, at most N Lean processes at a time.

Usage: python scripts/check.py PrincipiaMathematica/Part1/SectionA.lean [more files] [--slots 3] [--no-deps]

Before checking a file, the project modules it imports (`import PrincipiaMathematica.X`) are built
with `lake build` (one build at a time, under a lock), so that a file can be checked as soon as
the files it depends on compile. The slot limit keeps memory use bounded when several checks run
in parallel on one machine; any file, including a scratch file, can be checked this way.
"""
import argparse, os, re, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SLOT_DIR = Path(os.environ.get('TEMP', '/tmp')) / 'lean_slots_shared'


def pid_alive(pid: int) -> bool:
    """Whether a process with this id is running (never signals or kills it)."""
    if os.name == 'nt':
        import ctypes
        k32 = ctypes.windll.kernel32
        h = k32.OpenProcess(0x1000, False, pid)  # PROCESS_QUERY_LIMITED_INFORMATION
        if not h:
            return False
        code = ctypes.c_ulong()
        ok = k32.GetExitCodeProcess(h, ctypes.byref(code))
        k32.CloseHandle(h)
        return bool(ok) and code.value == 259  # STILL_ACTIVE
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def stale(p: Path) -> bool:
    """A lock is stale if its owner has exited, or if it is more than an hour old."""
    try:
        pid = int(p.read_text().strip() or '0')
    except (OSError, ValueError):
        pid = 0
    try:
        old = time.time() - p.stat().st_mtime > 3600
    except OSError:
        return False
    return old or (pid > 0 and not pid_alive(pid))


def acquire(name: str, n: int) -> Path:
    SLOT_DIR.mkdir(parents=True, exist_ok=True)
    while True:
        for i in range(n):
            p = SLOT_DIR / f'{name}{i}'
            try:
                if p.exists() and stale(p):
                    p.unlink()
            except OSError:
                pass
            try:
                fd = os.open(p, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
                os.write(fd, str(os.getpid()).encode())
                os.close(fd)
                return p
            except FileExistsError:
                continue
        time.sleep(2)


def build_deps(f: Path) -> int:
    mods = re.findall(r'^import (PrincipiaMathematica\.[\w.]+)', f.read_text(encoding='utf-8'), re.M)
    if not mods:
        return 0
    lock = acquire('build', 1)
    slot = acquire('slot', 3)
    try:
        r = subprocess.run(['lake', 'build', *mods], cwd=ROOT, capture_output=True, text=True,
                           encoding='utf-8', errors='replace')
    finally:
        slot.unlink(missing_ok=True)
        lock.unlink(missing_ok=True)
    if r.returncode != 0:
        print(f'[FAIL] building imports {mods} of {f}:')
        print('\n'.join(l for l in (r.stdout + r.stderr).splitlines() if 'error' in l.lower())[:4000])
    return r.returncode


def main() -> int:
    sys.stdout.reconfigure(encoding='utf-8')  # Lean diagnostics contain non-ASCII
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('--slots', type=int, default=3)
    ap.add_argument('--no-deps', action='store_true')
    a = ap.parse_args()
    ready = ROOT / '.lake' / 'packages_ready'
    if not ready.exists():
        print('waiting for the mathlib packages to finish copying …', flush=True)
        while not ready.exists():
            time.sleep(10)
    rc = 0
    for f in a.files:
        path = Path(f) if Path(f).is_absolute() else ROOT / f
        if not a.no_deps and build_deps(path) != 0:
            rc = 1
            continue
        slot = acquire('slot', a.slots)
        try:
            t0 = time.time()
            r = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, capture_output=True,
                               text=True, encoding='utf-8', errors='replace')
        finally:
            slot.unlink(missing_ok=True)
        msg = (r.stdout + r.stderr).strip()
        sorries = msg.count("declaration uses `sorry`") + msg.count("declaration uses 'sorry'")
        print(f"[{'OK' if r.returncode == 0 else 'FAIL'}] {f} ({time.time() - t0:.0f}s, sorry warnings: {sorries})")
        if msg:
            print(msg)
        rc |= r.returncode != 0
    return rc


if __name__ == '__main__':
    sys.exit(main())
