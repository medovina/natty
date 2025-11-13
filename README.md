## Natty

Natty is a natural-language proof assistant with an embedded automatic prover for higher-order logic.  It can read input containing axioms, definitions, and theorems written in natural language with a restricted vocabulary and grammer.  Any theorem in the input may optionally include a proof, also written in natural language.  Natty translates the input into a series of statements of higher-order logic, and attempts to prove the input theorems automatically.

Natty's automatic prover is based on a subset of the higher-order superposition calculus[^1].

Natty is in an early stage of development, and is currently only able to prove some basic identities about the natural numbers and integers.  As such, in its present form it will probably be of interest only to theorem proving researchers and enthusiasts.

### Prerequsities

Natty is written in [OCaml](https://ocaml.org/), using [Dune](https://dune.build/) as its build system.  It requires OCaml version 5.4 and depends on several OCaml libraries: [MParser](https://github.com/murmour/mparser), [psq](https://github.com/pqwy/psq), and [yojson](https://github.com/ocaml-community/yojson).  You can install these libraries using [opam](https://opam.ocaml.org/):

```
$ opam install mparser mparser-re psq yojson
```

### Running Natty

Natty's math library contains several files that develop some basic mathematics:

* [nat.n](math/nat.n) - defines the natural numbers using the Peano axioms, then asserts many identities about them
* [int.n](math/int.n) - defines the integers using the natural numbers, then asserts many identities about them
* [set.n](math/set.n) - contains a few definitions about functions and sets
* [num.n](math/num.n) - a development of elementary number theory including the infinite of primes

Natty can prove most of the theorems in these files.  (There are also files `nat1.n`, `int1.n` and `num1.n` containing more mathematics that Natty cannot yet verify, though I am working on that.)

You can run Natty on any of these files from the command line.  For example:

```
$ ./natty math/nat.n
```

By default, Natty will attempt to prove theorems only in the module (e.g. `nat.n`) that you have specified.  The `-m` option asks Natty to also prove theorems in all modules that the given module uses (recursively).

The `-p` option asks Natty to output a proof of each theorem that it proves:

```
$ ./natty -p math/nat.n
```

The `-d` option will print verbose debug output, showing all inferences that Natty makes as it searches for proofs.

By default, Natty will stop as soon as it fails to prove any theorem.  The `-a` option asks it to keep going and attempt to prove all theorems even if one or more proofs fail.

The `-t` option specifies a time limit for searching for a proof.  For example, `-t2` specifies a limit of 2 seconds.  The default limit is 5 seconds.

The `-x` option will cause Natty to export each theorem from the input file (and its dependencies) to a file in the standard THF format.  The output files will appear in the `thf` subdirectory, e.g. in the `thf/nat` directory for theorems from `nat.n`.  In this mode Natty will not attempt to prove any theorems.

You can also run Natty on a THF file directly:

```
$ ./natty thf/nat/1.thf
```

To see a list of other available options, run Natty with no command-line arguments:

```
$ ./natty
```

### Documentation

At this stage there is basically none, aside from what you see in this README file.  I'll try to improve this over time.

Reading [`nat.n`](nat.n) and other input files may give you an idea of the syntactic constructs that Natty currently understands.  You could try running Natty on your own input file with custom axioms and theorems, but be warned that syntax not already present in `nat.n` or other files is very unlikely to work.

### Evaluation

The Python program `eval.py` evaluates Natty and several other provers (E, Vampire, Zipperposition) on a set of THF files.  To use it, first use Natty to export the theorems from `nat.n` to THF files:

```
$ natty -x math/nat.n
```

After that, run

```
$ python eval.py -pnatty thf/nat
```

That will run Natty on all the THF files in the `nat` subdirectory, and generate a results file `nat_results.csv` that you can open in any spreadsheet program.  After '-p' you may alternately specify the name of a different prover to evaluate, one of 'e', 'vampire' or 'zipperposition'.  Any such prover will need to be in your `PATH`. To evaluate all of these provers at once, run

```
$ python eval.py -a thf/nat
```

### References

[^1]: Bentkamp, Alexander, et al. "Superposition for higher-order logic." _Journal of Automated Reasoning_ 67.1 (2023): 10.
