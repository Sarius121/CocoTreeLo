# CocoTreeLo: Model-Checking First-Order CTL in Multiset Rewrite Systems

## Installation

### Install and Configure OCaml

- Install `opam`: `https://opam.ocaml.org/doc/Install.html`
- Create opam switch with OCaml version 5.4.1:
    ```
    opam switch create . 5.4.1
    eval $(opam env)
    ```

### Installing dependencies & Building

Most dependencies can be built with:
```
dune build @opam --auto-promote
opam install . --deps-only
dune build
```

Additionally, the implementation uses [Maude](https://maude.cs.illinois.edu/) 3.5.1.
It can be downloaded from their website, and should be placed into the `extlib/custom-maude` folder.
However, one dependency of Maude (BuDDy) currently has a bug that makes our implementation crash on some inputs.
The folder `extlib/custom-maude` contains a prebuilt Maude version where this bug has been fixed.
However, the bug has not been fixed by the maintainers, and we only provide the built tool.
So, if you use the fixed Maude version, you do it at your own risk (as everything else as well).

## Running
```
dune exec -- cocotreelo <program-file> <ctl-file>
```
The formats for these input files are described in [Program Input Format](#program-input-format).

Optional Arguments:
- `-r <i>`: In the model-checking phase, update the annotations at most i times per strongly connected component in the product structure.
- `-c <i>`: Run the abstraction-refinement cycle at most i times.
- `-v`: Output intermediate steps.
- `-o`: Output intermediate results as dot graphs to files, e.g., the encoding or product structure.
    This only works in combination with `-v`.
    The following intermediate results are outputted for every cycle `i` (the table assumes that the input file is named `program.spthy`):
    | Step | Output File | Comments
    |---|---|---|
    | FO-KMTS encoding | `program_out/<i>-kripke.dot` | Only if the program file is a multiset rewrite system
    | Product structure | `program_out/<i>-tab.dot` |
    | Annotated product structure after step `j` | `program_out/<i>-ann-<j>.dot` |
    | Maybe-Reason graph | `program_out/<i>-maybe-reason.dot` |
- `-t`: Print running-time statistics at several points in between.
    The running-times are accumulated over the complete run.
- Additionally, you can set manual initial encoding parameters in the file `lib/encoding/manual_params.ml`.
    You find an examples for this in `bpmn/auto-test`.

### Drawing Outputted Graphs

You can draw the outputted .dot graphs with the `draw.sh` script.
With `draw.sh file.dot`, you can draw individual files.
With `draw.sh dir/`, you can draw all .dot files in the directory `dir`.

Alternatively, you can use the Graphviz Interactive Preview extension for VSCode ([Link to the extension](https://marketplace.visualstudio.com/items?itemName=tintinweb.graphviz-interactive-preview)).

## Program Input Format

Example input files are in the [examples/](examples/).

### FO-CTL Properties

The FO-CTL file has to contain one FO-CTL property in the first line, followed by a line break (!).
E.g.:
```
FORALL x. AG (!P(x) || EX Q(x))

```
The syntax supports the usual CTL operators (`AX`, `EF`, ...), quantifiers `FORALL` and `EXISTS` and logical operators `&&` and `||`.
Additionally, you can check existence of facts with `F(t1,...,tk)` and non-existence with `!F(t1,...,tk)`.
Boolean formulas have to be provided in SMTLib2 format in quotes (e.g., `"(= x 5)"`).

Example files can be found in [examples/properties/](examples/properties/).

The implementation contains no type-checker, so you have to make sure that the files are valid.
E.g., free variables and quantifiers with equal variables are not supported.

### Multiset Rewrite Systems

Multiset rewrite systems are given as `.spthy` files, whose format is similar to the Tamarin input.
The difference is that currently only rules can be defined.
Also, there are no pre-defined facts like `Fr`.
If you want to introduce a fresh variable, you can just introduce them on the right-hand side of a rule.

An example is the following file:
```
theory Rule12
begin
rule Rule1:
    [ ]
    -->
    [ P(x) ]
rule Rule2:
    [ P(x) ]
    -->
    [ Q(x) ]
end
```

More example files can be found in [examples/msrs/](examples/msrs/).

The implementation contains no type-checker, so you have to make sure that the files are valid.
E.g., no two rules can have the same name.


## Evaluation

You can run the evaluation of the simple test cases with
```
dune exec -- bin/eval.exe
```

The BPMN test cases can be found in the `bpmn` folder.
The can be automatically run with the correct initial parameters by calling:
```
./bpmn/auto-test/run-tests.sh
```
Note that this script copies manual params into `lib/encoding/manual_params.ml`.
You should reset this file after running the tests.

## Tests

The tests can be run with:
```
dune exec -- test/test_cocotreelo.exe
```

The source files also include some inline expect-tests that can be run with `dune test`.

## Other Remarks

- The implementation can generate counterexamples for some properties.
    However, this feature is experimental.
- If you use the tool, you do this at your own risk.
