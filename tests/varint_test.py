"""Exact signed integer widths, conversions, containers and named type identity."""
from pathlib import Path
import subprocess
import sys
import tempfile

compiler, clang = (str(Path(arg).resolve()) for arg in sys.argv[1:])
with tempfile.TemporaryDirectory(prefix='ocean-varint-') as directory:
    root = Path(directory)
    source, ir, executable = root / 'main.oc', root / 'main.ll', root / 'program'

    def check(body, message=None):
        source.write_text('package main;\n' + body)
        result = subprocess.run([compiler, 'build', '--check', str(source)], capture_output=True, text=True)
        assert (result.returncode == 0) == (message is None), result.stderr
        if message:
            assert message in result.stderr, result.stderr

    def program(body, status=0):
        check(body)
        result = subprocess.run([compiler, 'build', str(source), '--emit-llvm', '-o', str(ir)], capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
        for opt in ('-O0', '-O2'):
            result = subprocess.run([clang, opt, '-Wno-override-module', str(ir), '-o', str(executable), '-lffi'], capture_output=True, text=True)
            assert result.returncode == 0, result.stderr
            result = subprocess.run([str(executable)])
            assert result.returncode == status, (body, result.returncode)

    program('''type nibble varint(4); type Alias = nibble;
func identity(x varint(6)) varint(6) { return x; }
func main() int {
    n := 7->nibble; n++; n += 1->Alias;
    x: varint(6) = -12; a: [2]varint(4) = {2, -3};
    p := &x; *p = -11;
    b: any = x; y := b.(varint(6));
    if (sizeof(varint(4)) != 1 || sizeof(nibble) != 1) return 1;
    if (n->int != -7 || identity(y)->int != -11 || a[1]->int != -3 || x != -11 || a[0] != 2) return 2;
    z := zero(varint(9));
    literal := [2]varint(4){1, 2}; dynamic := []varint(4){3, 4};
    if (literal[0] != 1 || dynamic[1] != 4) return 3;
    return z->int;
}''')
    body = []
    for width in range(1, 65):
        minimum = -(1 << (width - 1))
        maximum = (1 << (width - 1)) - 1
        body.append(f'a{width}: varint({width}) = {minimum}; b{width}: varint({width}) = {maximum};')
        body.append(f'if (a{width}->int != {minimum} || b{width}->int != {maximum}) return 1;')
        body.append(f'b{width}++; if (b{width}->int != {minimum}) return 2;')
    program('func main() int {\n' + '\n'.join(body) + '\nreturn 0; }')
    for width in (0, 8388609, -1):
        check(f'func main() {{ x: varint({width}); }}', 'varint width')
    check('func main() { x: varint(4) = 8; }', 'type mismatch')
    check('func main() { x: varint(6) = 3; y: varint(4) = x; }', 'type mismatch')
    check('type nibble varint(4); func main() { x: nibble = 3; }', 'type mismatch')
    check('func main() { x: varint; }', 'varint requires')
    # Array and pointer modifiers are prefixes; postfix forms name the prefix spelling.
    for body, suggestion in (
        ('func main() { x: varint(4)[2] = {1, 2}; }', "'[2]varint(4)'"),
        ('func main() { x := varuint(4)[]{1}; }', "'[]varuint(4)'"),
        ('func main() { x: varint(8)* = null; }', "'*varint(8)'"),
        ('func main() { x: varint(4)[2][3]; }', "'[3][2]varint(4)'"),
        ('func f(x varuint(4)[]) {} func main() {}', "'[]varuint(4)'"),
    ):
        check(body, suggestion)
    source.write_text('package main;\nfunc f(x varuint(4)[]) {}\n'
                      'func main() { a: varint(4)[2] = {1, 2}; b := varint(4)[2]{3, 4}; p: varuint(8)* = null; }\n')
    result = subprocess.run([compiler, 'fix', str(source)], capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    assert source.read_text() == ('package main;\nfunc f(x []varuint(4)) {}\n'
                                  'func main() { a: [2]varint(4) = {1, 2}; b := [2]varint(4){3, 4}; p: *varuint(8) = null; }\n'), source.read_text()
    check(source.read_text()[len('package main;\n'):])
    # varint and varuint are keywords: they cannot name anything.
    for body, message in (
        ('func main() { varint := 2; }', 'varint requires a bit width'),
        ('func main() { x := 1; y := varuint; }', 'varuint requires a bit width'),
        ('func f(varint int) {} func main() {}', 'varint requires a bit width'),
        ('struct S { varuint int; } func main() {}', 'Expected struct field name'),
        ('type varint int; func main() {}', 'Expected type name'),
        ('func varuint() {} func main() {}', 'Expected function name'),
    ):
        check(body, message)
    # C variadic arguments use the default promotions: odd widths sign-extend
    # (varint) or zero-extend (varuint) to int/long long rather than passing iN.
    program('''extern i32 snprintf(buffer<i8> out, int size, buffer<i8> format, ...);
func main() int {
    out := [100]i8; a: varint(6) = -1; b: varint(40) = -5; c: varuint(40) = 1099511627775; d: varint(17) = -65536;
    n := extern.snprintf(out.data, len(out), "%d %lld %llu %d %d\\0".data, a, b, c, d, true);
    s := ""; for (i := 0; i < n; i++) s += out[i];
    if (s != "-1 -5 1099511627775 -65536 1") return 1;
    return 0; }''')
    # C has no integers other than 8, 16, 32, and 64 bits wide, so externs cannot declare them.
    for body in (
        'extern i32 abs(varint(6) x); func main() {}',
        'extern varuint(12) f(); func main() {}',
        'type nibble varint(4); extern void g(nibble x); func main() {}',
        'type small = varuint(3); extern void g(small x); func main() {}',
    ):
        check(body, 'C has no')
    check('extern i32 abs(varint(32) x); extern varuint(64) h(varint(8) a, varuint(16) b); func main() {}')
    # Widths above 64 bits are rejected in extern signatures even if never called.
    check('extern varint(65) f(); func main() {}', 'C has no 65-bit integer type')
    check('type W = varuint(128); extern void g(W x); func main() {}', 'C has no 128-bit integer type')
    # An assignment's value has the destination's type: z := (x = y) is varint(16), not varint(8).
    program('''func main() int {
    x: varint(16); y: varint(8) = 127; z := (x = y); z++;
    boxed: any = z; f: float; g: f32 = 1.5; h := (f = g); hb: any = h;
    if (z->int != 128 || boxed.(varint(16)) != 128 || hb.(float) != 1.5) return 1;
    return 0; }''')
