"""Arbitrary-width signed and unsigned integers, exact literals and boxed storage."""
from pathlib import Path
import subprocess
import sys
import tempfile

compiler, clang = (str(Path(arg).resolve()) for arg in sys.argv[1:])
with tempfile.TemporaryDirectory(prefix='ocean-wide-') as directory:
    root = Path(directory)
    source, ir, executable = root / 'main.oc', root / 'main.ll', root / 'program'

    def run(*args):
        return subprocess.run(args, capture_output=True, text=True, timeout=90)

    def emit(body):
        source.write_text('package main;\n' + body)
        result = run(compiler, 'build', str(source), '--emit-llvm', '-o', str(ir))
        assert result.returncode == 0, result.stderr
        return ir.read_text()

    def program(body):
        emit(body)
        for opt in ('-O0', '-O2'):
            result = run(clang, opt, '-Wno-override-module', str(ir), '-o', str(executable), '-lffi')
            assert result.returncode == 0, result.stderr
            result = run(str(executable))
            assert result.returncode == 0 and result.stderr == '', (body, result)

    def rejected(body, message):
        source.write_text('package main;\n' + body)
        result = run(compiler, 'build', '--check', str(source))
        assert result.returncode != 0 and message in result.stderr, result

    for width in (65, 66, 80, 127, 128, 129, 192, 256, 257, 511, 512, 1024):
        maximum, minimum = (1 << width) - 1, -(1 << (width - 1))
        program(f'''func id(x varuint({width})) varuint({width}) {{ return x; }}
func main() int {{
    x: varuint({width}) = {maximum}; y: varint({width}) = {minimum};
    if (x != {maximum} || y != {minimum}) return 1;
    x++; y--; if (x != 0 || y != {(1 << (width - 1)) - 1}) return 2;
    x--; y++; if (x != {maximum} || y != {minimum}) return 3;
    b: any = id(x); z := b.(varuint({width})); if (z != x) return 4;
    c: any = y; d := c.(varint({width})); if (d != y) return 5;
    return 0;
}}''')

    program('''func main() int {
    x: varint(128) = -9223372036854775809;
    y: varint(65) = -18446744073709551615;
    if (x != -9223372036854775809 || y != -18446744073709551615) return 1;
    if (x->varuint(128) != 340282366920938463454151235394913435647) return 2;
    z := -(-18446744073709551615); b: any = z;
    if (b.(uint) != 18446744073709551615) return 3;
    return 0;
}''')

    program('''type Big varuint(256);
func divide(x varuint(256), y varuint(256)) (varuint(256), varuint(256)) { return x / y, x % y; }
func signedDivide(x varint(256), y varint(256)) varint(256) { return x / y; }
func main() int {
    x: varuint(256) = 340282366920938463463374607431768211456;
    y: varuint(256) = 0x100000000000000000000000000000001;
    binary: varuint(128) = 0b10000000000000000000000000000000000000000000000000000000000000000;
    octal: varuint(128) = 0o2000000000000000000000;
    if (binary != octal || x + 1 != y || (x >> 128) != 1) return 1;
    q, r := divide(y, 3); if (q != 113427455640312821154458202477256070485 || r != 2) return 2;
    if (signedDivide(-340282366920938463463374607431768211456, 2) != -170141183460469231731687303715884105728) return 3;
    n := y->Big; box: any = n; back := box.(Big); if (back != n) return 4;
    narrow := y->varuint(128); if (narrow != 1) return 5;
    small: varuint(65) = 18446744073709551616; large: varuint(256) = small;
    neg: varint(65) = -18446744073709551616; signed: varint(256) = neg;
    if (large != 18446744073709551616 || signed != -18446744073709551616) return 6;
    if ((large->float) != 18446744073709551616.0) return 7;
    return 0;
}''')

    program('''func identity<T any>(x T) T { return x; }
func add<T ~varuint(256)>(a T, b T) T { return a + b; }
func main() int {
    a: varuint(128) = 340282366920938463463374607431768211455;
    b: varuint(256) = 1; c := a + b;
    if (sizeof(c) != sizeof(varuint(256)) || c != 340282366920938463463374607431768211456) return 1;
    s: varint(128) = -1; combined := a + s;
    if (combined != 340282366920938463463374607431768211454 || sizeof(combined) != sizeof(varint(129))) return 2;
    if (add<varuint(256)>(identity<varuint(256)>(c), b) != 340282366920938463463374607431768211457) return 3;
    return 0;
}''')

    program('''struct Record { value varuint(256); signed varint(129); }
struct Bits { a varuint(128) : 4; b varint(256) : 5; }
func copy(x Record) Record { return x; }
func main() int {
    x := Record{340282366920938463463374607431768211456, -18446744073709551616};
    a: [2]Record = {x, copy(x)}; a[1].value++;
    if (a[0].value + 1 != a[1].value) return 1;
    dynamic: []varuint(256) = {x.value}; dynamic += x.value + 1;
    if (dynamic[1] != a[1].value) return 2;
    box: any = x; y := box.(Record); if (y != x) return 3;
    boxes: []any = {x.value, y.value}; if (boxes[0] != boxes[1]) return 4;
    m: map[varuint(256)]int = {}; m[x.value] = 9;
    if (m[y.value] != 9) return 5;
    b := Bits{15, -16}; b.a++; b.b++; if (b.a != 0 || b.b != -15) return 6;
    p := new(varuint(256)); *p = dynamic[1]; if (*p != dynamic[1]) return 7;
    return 0;
}''')

    program('''type Count varuint(256);
func (c Count) Get() Count { return c; }
interface Getter { Get() Count; }
func closure(x varuint(256)) func() varuint(256) { return func() varuint(256) { x++; return x; }; }
func main() int {
    n := 340282366920938463463374607431768211456->Count;
    g: Getter = n; if (g.Get() != n) return 1;
    next := closure(n->varuint(256)); if (next() != 340282366920938463463374607431768211457) return 2;
    if (next() != 340282366920938463463374607431768211458) return 3;
    return 0;
}''')

    for family in ('varint', 'varuint'):
        text = emit(f'func accept(x {family}(8388608)) {{}} func main() int {{ accept(zero({family}(8388608))); return 0; }}')
        assert 'i8388608' in text
        result = run(clang, '-Wno-override-module', '-S', '-emit-llvm', '-x', 'ir', str(ir), '-o', str(root / 'verified.ll'))
        assert result.returncode == 0, result.stderr
        for width in (0, 8388609, -1, 18446744073709551617):
            rejected(f'func main() {{ x: {family}({width}); }}', 'width')
    rejected('func main() { x: varint(128) = 170141183460469231731687303715884105728; }', 'out of range')
    rejected('func main() { x: varint(128) = -170141183460469231731687303715884105729; }', 'out of range')
    rejected('func main() { x: varuint(128) = 340282366920938463463374607431768211456; }', 'out of range')
    rejected('func main() { x: varuint(128) = -1; }', 'out of range')
    rejected('func main() { x: varuint(256) = 1; y: varuint(128) = x; }', 'type mismatch')
    rejected('extern int f(int x, ...); func main() { x: varuint(128) = 1; extern.f(1, x); }', 'C interoperability')

    # Wide literals round once, directly to f32 (2^80 + 2^56 + 1 -> 2^80 + 2^57, not 2^80).
    program('''func main() int {
    x: f32 = 1208925891672223212634113; up := 1208925963729817250562048->f32;
    if (x != up || x == 1208925819614629174706176->f32 || 1208925891672223212634113->f32 != up) return 1;
    return 0; }''')

    # Literals too large for their float destination warn, except for an explicit ->f64 cast.
    def diagnostics(body):
        source.write_text('package main;\n' + body)
        result = run(compiler, 'build', '--check', str(source))
        assert result.returncode == 0, result.stderr
        return result.stderr
    big, f32big = '0x1' + '0' * 256, '0x1' + '0' * 32
    for body, width in ((f'func main() {{ x: float = {big}; }}', 'f64'),
                        (f'func main() {{ x: f32 = {f32big}; }}', 'f32'),
                        (f'func main() {{ x: f32 = -{f32big}; }}', 'f32'),
                        (f'func main() {{ x := {big}->f32; }}', 'f32'),
                        (f'func main() {{ x := {f32big}->f32; }}', 'f32')):
        stderr = diagnostics(body)
        assert 'warning:' in stderr and f'out of range for {width}' in stderr, (body, stderr)
    for body in (f'func main() {{ x := {big}->f64; }}', f'func main() {{ x := {big}->float; }}',
                 f'func main() {{ x := {f32big}->f64; y: f32 = 340282346638528859811704183484516925440; }}'):
        assert 'warning:' not in diagnostics(body), body

    # Decimal literals convert subquadratically: a million digits (~3.3M bits) emits in about a
    # second, where digit-by-digit conversion took minutes. Clang time is excluded.
    import time
    source.write_text('package main;\nfunc main() { x := 1' + '0' * 1000000 + '; }\n')
    started = time.time()
    result = run(compiler, 'build', str(source), '--emit-llvm', '-o', str(ir))
    assert result.returncode == 0 and time.time() - started < 20, (result.stderr, time.time() - started)
    rejected('func main() { x := 1' + '0' * 2525223 + '; }', 'exceeding 8388608 bits')

    # Identical types keep their type; one signedness takes the wider operand (equal widths:
    # the standard type); mixed signedness grows only when both are varint/varuint. The
    # analyzed type matches the boxed runtime type.
    program('''func main() int {
    w8: varuint(8) = 5; u: u8 = 6; v32: varint(32) = 1; i: i32 = 2; s100: varint(100) = -7; u128: varuint(128) = 8;
    a: any = w8 + u; b: any = i + v32; c: any = w8 + w8; d: any = s100 + u128; e: any = u128 + s100;
    if (a.(u8) != 11 || b.(i32) != 3 || c.(varuint(8)) != 10) return 1;
    if (d.(varint(129)) != 1 || e.(varint(129)) != 1) return 2;
    return 0; }''')
    rejected('func main() { w8: varuint(8) = 5; u: u16 = 6; x: varuint(8) = w8 + u; }', 'type mismatch')

    program('''func main() int {
    x: any; y: varint(8) = 7; z := (x = y);
    wide: varuint(128) = 0x10000000000000001; w := (x = wide);
    if (z.(varint(8)) != 7 || w.(varuint(128)) != wide || x.(varuint(128)) != wide) return 1;
    return 0; }''')

    program(f'''func main() int {{
    exact: any = 16777216->varuint(25); rounded: any = 16777217->varuint(25);
    f: any = 16777216->f32; fractional: any = 0.5;
    huge: any = {1 << 1023}; sameHuge: any = {(1 << 1023)}->f64;
    bigger: any = {(1 << 1023) + 1}; negative: any = -1->int; negativeFloat: any = -1.0;
    zero: any = 0->uint; negativeZero: any = -0.0;
    infinity: any = {1 << 1024}->f64; nan: any = 0.0 / 0.0;
    if (exact != f || f != exact || rounded == f || f == rounded) return 1;
    if (huge != sameHuge || bigger == sameHuge || negative != negativeFloat) return 2;
    if (zero == fractional || zero != negativeZero || zero == nan || huge == infinity) return 3;
    values := map[any]int{{exact: 1, rounded: 2}};
    if (values[f] != 1 || len(values) != 2) return 4;
    return 0; }}''')
