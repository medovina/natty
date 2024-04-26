## Natty

Natty is a natural-language proof assistant with an embedded automatic prover for higher-order logic.  It can read input containing axioms, definitions, and theorems written in natural language with a restricted vocabulary and grammer.  Any theorem in the input may optionally include a proof, also written in natural language.  Natty translates the input into a series of statements of higher-order logic, and attempts to prove the input theorems automatically.

Natty is in an early stage of development, and is currently only able to prove some basic identities about the natural numbers.  As such, in its present form it will probably be of interest only to theorem proving researchers and enthusiasts.

### Prerequsities

Natty is written in [OCaml](https://ocaml.org/), using [Dune](https://dune.build/) as its build system.  It depends on two OCaml libraries: [MParser](https://github.com/murmour/mparser) and [psq](https://github.com/pqwy/psq).  You can install these libraries using [opam](https://opam.ocaml.org/):

```
$ opam install mparser mparser-re psq
```

### Running

The included file [`nat.n`](nat.n) defines the natural numbers using the Peano axioms, and contains a number of elementary theorems about the naturals.  To invoke Natty on this file, run

```
$ ./natty nat.n
```

The `-p` option asks Natty to output a proof of each theorem that it proves:

```
$ ./natty -p nat.n
```

The `-d` option will print verbose debug output, showing all inferences that Natty makes as it searches for proofs.

By default, Natty will stop as soon as it fails to prove any theorem.  The `-k` option asks it to keep going and attempt to prove all theorems even if one or more proofs fail.  (At this time Natty is not able to prove all theorems in `nat.n`, so you will need to use this option if you'd like it to try to prove all theorems in that file.)

The `-t` option specifies a time limit for searching for a proof.  For example, `-t5` specifies a limit of 5 seconds.

The `-x` option will cause Natty to export each theorem from the input to a file in the standard THF format.  The output files will appear in a subdirectory, e.g. in the `nat` directory for theorems from `nat.n`.  In this mode Natty will not attempt to prove any theorems.

You can also run Natty on a THF file directly:

```
$ ./natty nat/1.thf
```

To see a list of other available options, run Natty with no command-line arguments:

```
$ ./natty
```

### Documentation

At this stage there is basically none, aside from what you see in this README file.  I'll try to improve this over time.

Reading [`nat.n`](nat.n) may give you an idea of the syntactic constructs that Natty currently understands.  You could try running Natty on your own input file with custom axioms and theorems, but be warned that syntax not already present in `nat.n` is very unlikely to work.

### Evaluation

The Python program `eval.py` evaluates Natty and several other provers (E, Vampire, Zipperposition) on a set of THF files.  To use it, first use Natty to export the theorems from `nat.n` to THF files:

```
$ natty -x nat.n
```

After that, run

```
$ python eval.py nat
```

That will run all of these provers on all the THF files in the `nat` subdirectory, and generate a results file `nat_results.csv` that you can open in any spreadsheet program.

To use this script, you will need to have E, Vampire, and Zipperposition installed and available in your `PATH`.  To omit any of these provers (or add more), edit `eval.py` and adjust the `provers` list at the top of the file.
