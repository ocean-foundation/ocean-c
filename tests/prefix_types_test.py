"""Prefix type syntax, diagnostics for removed postfix syntax, and `ocean fix`."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

compiler = str(Path(sys.argv[1]).resolve())
checks = 0
environment = dict(os.environ, OCEAN_BUILD_CACHE="off")


def run(args, cwd=None):
    return subprocess.run(args, capture_output=True, text=True, timeout=60, cwd=cwd, env=environment)


with tempfile.TemporaryDirectory(prefix="ocean prefix types ") as directory:
    root = Path(directory)

    def program(text, status=0):
        global checks
        package = root / f"program{checks}"
        package.mkdir()
        (package / "main.oc").write_text("package main;\n" + text)
        result = run([compiler, "run", str(package)])
        assert result.returncode == status, (text, result)
        checks += 1

    def legacy(text, message):
        global checks
        package = root / f"legacy{checks}"
        package.mkdir()
        (package / "main.oc").write_text("package main;\nstruct Node { v int; }\n" + text)
        result = run([compiler, "check", str(package)])
        assert result.returncode == 1 and message in result.stderr, (text, message, result.stderr)
        checks += 1

    # Every modifier precedes the type it modifies; the last suffix of the old
    # syntax is now the first prefix.
    program('''struct Node { v int; next *Node; }
struct Matrix(h, w int) { data [w][h]int; }
func total(ps []*int) int { t := 0; for (_, p := range ps) { t += *p; } return t; }
func main() int {
    x := 5; y := 6;
    if (total([]*int{&x, &y}) != 11) return 1;
    grid: [3][2]int;
    if (len(grid) != 3 || len(grid[0]) != 2) return 2;
    counted := [...]int{1, 2, 3};
    dyn := [4]int;
    if (len(counted) != 3 || len(dyn) != 4) return 3;
    raw: buffer<int, 4> = {1, 2};
    n := 3;
    runtime: buffer<int, n>;
    heap := buffer<int, n * 2>;
    heap[5] = 1;
    if (raw[1] != 2 || len(raw) != 4 || len(heap->buffer<int, 2>) != 2) return 4;
    maps: []map[string]int = {map[string]int{"a": 1}};
    calls: []func() int = {func() int { return 4; }};
    if (maps[0]["a"] != 1 || calls[0]() != 4) return 5;
    m := map[string][]int{"k": {1, 2}};
    lit := []int{1, 2, 3};
    q: *[]int = &lit;
    if (len(*q) != 3) return 6;
    mat := Matrix{2, 3};
    if (len(mat.data) != 3 || len(mat.data[0]) != 2) return 7;
    nodes := []*Node{&Node{1, null}};
    if (nodes[0].v != 1 || sizeof([3]int) != 32) return 8;
    mixedValues := mixed []any{1, "two"};
    v: any = lit;
    got, ok := v.([]int);
    if (!ok || len(got) != 3 || len(mixedValues) != 2) return 9;
    return 0;
}''')

    # Removed postfix syntax reports the prefix spelling.
    array = "Square brackets go before the type for an array. Did you mean "
    legacy("func main() { x: int[]; }", array + "'[]int'?")
    legacy("func main() { x: int[3][2]; }", array + "'[2][3]int'?")
    legacy("func main() { x := int[]{1, 2}; }", array + "'[]int'?")
    legacy("func main() { x := int[...]{1, 2}; }", array + "'[...]int'?")
    legacy("func main() { n := 3; x := int[n]; }", array + "'[n]int'?")
    legacy("func main() { x := Node[2]; }", array + "'[2]Node'?")
    legacy("func main() { x: mixed any[]; }", array + "'mixed []any'?")
    legacy("func f(x Node*[]) {}", array + "'[]*Node'?")
    legacy("func main() { x: map[string]int[]; }", array + "'[]int'?")
    legacy("func main() { x: Node*; }", "The pointer star goes before the type. Did you mean '*Node'?")
    legacy("func main() { x: buffer<int>[4]; }",
           "A buffer's size is its second type argument. Did you mean 'buffer<int, 4>'?")
    legacy("func main() { x := Node[]{}; }", array + "'[]Node'?")
    legacy("func main() { x: buffer<int>[]; }",
           "A buffer's size is its second type argument. Did you mean 'buffer<int>'?")

    # Function types require func before the parameter list.
    legacy("type Callback = int(int);", "Expected semicolon")
    legacy("type Callback = (int, bool)(int);", "Expected function signature type")
    program("""type Callback = func(int) (int, bool);
func main() int {
    f: Callback = func(n int) (int, bool) { return n, true; };
    n, ok := f(3);
    if (!ok) return 1;
    return n - 3;
}""")

    # Test raw addresses without dereferencing them, and use an array for
    # scaled offsets, element differences, and pointer updates.
    program("""global: *int = 0x5;
type Ptr *int;
struct Entry { tag i8; value int; }
func main() int {
    ip: *int = 5;
    inferred := 5->(*int);
    rawAddress := 5;
    fromVariable: *int = rawAddress;
    callback: *func() = 0;
    if (inferred != ip || fromVariable != ip || callback->uint != 0) return 8;
    if (ip->uint != 5 || global->uint != 5) return 1;
    ip = 0->(*int);
    if (ip->uint != 0 || ip == null) return 2;
    a := [3]int{10, 20, 30};
    p := &a[0];
    q := 2 + p;
    if (*q != 30 || q - p != 2 || p - q != -2) return 3;
    if (*(p++) != 10 || *p != 20 || *(++p) != 30) return 4;
    p -= 2;
    p += 1;
    if (*p != 20 || *(p--) != 20 || *p != 10) return 5;
    *p = 15;
    if (a[0] != 15 || *(q - 1) != 20) return 6;
    alias: Ptr = 5->Ptr;
    alias++;
    if (alias->uint != 13) return 7;
    records := [2]Entry{Entry{1, 10}, Entry{2, 20}};
    first := &records[0];
    if ((first + 1).value != 20 || (first + 2) - first != 2) return 9;
    return 0;
}""")
    legacy("func main() { p: *void; p += 1; }", "invalid pointer arithmetic operands")
    legacy("func main() { p: *int; p += p; }", "invalid pointer arithmetic operands")
    legacy("func main() { p: *int; p -= p; }", "invalid pointer arithmetic operands")
    legacy("func main() { p: *int = 1.5; }", "type mismatch")
    legacy("func main() { *int ip = 5; }", "Expected semicolon")
    legacy("func main() { ip: *int 5; }", "Expected semicolon")
    legacy("func main() { ip: *int; ip = 5; }", "type mismatch")

    pointer_parameter = "func address(p *int) int { return p->int; } "
    legacy(pointer_parameter + "func main() { address(5); }", "type mismatch")
    legacy(pointer_parameter + "func main() { n := 5; address(n); }", "type mismatch")
    legacy(pointer_parameter + "func main() { f := address; f(5); }", "type mismatch")
    legacy("extern void address(*int p); func main() { extern.address(5); }", "type mismatch")
    program(pointer_parameter + "func main() int { return address(5->(*int)) - 5; }")

    # A variable named like a type keyword is still indexable.
    program("func main() int { buffer := []int{4, 5}; return buffer[1] - 5; }")

    # ocean fix rewrites a package, including types imported from another package
    # and type parameters in generic bodies, and is idempotent.
    module = root / "module"
    (module / "shapes").mkdir(parents=True)
    (module / "app").mkdir()
    (module / "ocean.mod").write_text("module example.com/fix\n\nocean 0.1\n")
    (module / "shapes" / "shapes.oc").write_text(
        "package shapes;\nstruct Point { X, Y int; }\nfunc Origins(n int) Point[] { return Point[n]; }\n")
    (module / "app" / "main.oc").write_text('''package main;
import "example.com/fix/shapes";
struct Grid(rows int) { cells int[rows][2]; }
func copyAll<T>(items T[]) T[] { out := T[len(items)]; for (i, item := range items) { out[i] = item; } return out; }
func main() int {
    points := shapes.Point[3];
    more := shapes.Origins(2);
    grid := Grid{4};
    // Comments and spacing outside rewritten types are preserved.
    view: buffer<int>[4] = {1};
    raw := buffer<int>[len(points) * 2];
    nested := int[][]{{1}, {2, 3}};
    four := 4;
    pointers: int*[] = {&four};
    if (len(copyAll<int>(int[]{1, 2})) != 2 || len(more) != 2 || len(grid.cells) != 2) return 1;
    if (len(points) != 3 || len(nested[1]) != 2 || *pointers[0] != 4 || view[0] != 1) return 2;
    raw[5] = 1;
    return 0;
}
''')
    fixed = run([compiler, "fix", "./..."], cwd=module)
    assert fixed.returncode == 0, fixed
    assert "app/main.oc" in fixed.stdout and "shapes/shapes.oc" in fixed.stdout, fixed.stdout
    assert (module / "shapes" / "shapes.oc").read_text().endswith(
        "func Origins(n int) []Point { return [n]Point; }\n")
    text = (module / "app" / "main.oc").read_text()
    for expected in ("cells [2][rows]int;", "func copyAll<T>(items []T) []T { out := [len(items)]T;",
                     "points := [3]shapes.Point;", "view: buffer<int, 4> = {1};",
                     "raw := buffer<int, len(points) * 2>;", "nested := [][]int{{1}, {2, 3}};",
                     "pointers: []*int = {&four};", "// Comments and spacing outside"):
        assert expected in text, (expected, text)
    checks += 1
    result = run([compiler, "run", "./app"], cwd=module)
    assert result.returncode == 0, result
    again = run([compiler, "fix", "./..."], cwd=module)
    assert again.returncode == 0 and again.stdout == "", again
    checks += 2

print(f"{checks} prefix type checks passed")
