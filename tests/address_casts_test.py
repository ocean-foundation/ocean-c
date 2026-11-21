"""Buffer/pointer <-> integer address conversions (§7.5)."""
from pathlib import Path
import subprocess
import sys
import tempfile

compiler, clang = (str(Path(arg).resolve()) for arg in sys.argv[1:])
with tempfile.TemporaryDirectory(prefix='ocean-address-casts-') as directory:
    root = Path(directory)
    source, ir, executable = root / 'main.oc', root / 'main.ll', root / 'program'

    def program(body):
        source.write_text('package main;\n' + body)
        result = subprocess.run([compiler, 'build', str(source), '--emit-llvm', '-o', str(ir)], capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
        for opt in ('-O0', '-O2'):
            result = subprocess.run([clang, opt, '-Wno-override-module', str(ir), '-o', str(executable), '-lffi'], capture_output=True, text=True)
            assert result.returncode == 0, result.stderr
            result = subprocess.run([str(executable)])
            assert result.returncode == 0, (body, result.returncode)

    # A sized buffer converts to its storage address; an integer converts back
    # to a buffer view or pointer, including directly inside call arguments.
    program('''func first(b buffer<i8>) int { return b[0] -> int; }
func main() int {
    st: buffer<i8, 64>;
    st[19] = 42;
    st[48] = 7;
    x := st -> int;
    if (first(((st -> int) + 19) -> (buffer<i8>)) != 42) return 1;
    if (*(((st -> int) + 48) -> (*i8)) != 7) return 2;
    w := (x + 48) -> (buffer<i8, 4>);
    if (w[0] != 7) return 3;
    if (((st -> (*i8)) -> int) != x) return 4;
    q := (x + 19) -> (buffer<i8>);
    if (q[0] != 42) return 5;
    *(((st -> int) + 3) -> (*i8)) = 9;
    v := ((st -> int) + 5) -> (buffer<i8>);
    v[0] = 11;
    if (st[3] != 9 || st[5] != 11) return 6;
    return 0;
}
''')
