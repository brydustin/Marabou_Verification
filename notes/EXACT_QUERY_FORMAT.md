# Exact query text format with a HOL-defined decoder

Completed on 2026-09-23. This is the first step of roadmap item B in
[CLAUDE_HANDOFF.md](../CLAUDE_HANDOFF.md): a narrow exact representation of
linear/ReLU queries whose meaning is a decoder written in Isabelle/HOL.
Theorems can now be stated about the bytes of such a file, not only about
HOL data produced by an untrusted adapter.

## What a text file means

[Exact_Query_Format.thy](../Isabelle/Exact_Query_Format.thy) defines
`decode_query :: nat list ⇒ rat_query option` on byte values. The accepted
language is:

```text
file      = "marabou-exact-query-v1" LF (statement LF)*
statement = kind (SP num SP var)* SP rel SP num     (eq with =, le with <=, ge with >=)
          | ("lower" | "upper") SP var SP num
          | "relu" SP var SP var                     (input, then output)
var       = "x" digits
num       = ["-"] digits [ "/" digits | "." digits ]
```

`SP` is byte 32 and `LF` byte 10. Tokens are separated by exactly one space,
every line including the last ends in `LF`, and there are no empty lines,
tabs, carriage returns, exponents, plus signs or non-ASCII bytes. Digits are
one or more of `0`–`9`.

Every number denotes an exact rational: `n`, `n/d` with `d>0`, or
`i.f = i + f/10^|f|`; a leading `-` negates. For example `0.50`, `1/2` and
`2/4` denote the same rational, and `-0` denotes 0. This is the existing
exact-decimal contract extended with fractions. A producer that wants to state
the value of a binary double must write that double's exact value (every
finite double has a finite exact decimal or dyadic fraction); nothing in the
format rounds.

A linear statement `eq a1 x1 … ak xk = b` denotes
`RatEq (RatExpr 0 [(a1,x1),…,(ak,xk)]) b`, and similarly for `le`/`ge`.
`lower x l` and `upper x u` denote `RatLower`/`RatUpper`; `relu x y` denotes
`ReLU x y`. Statement kinds may be interleaved; the query keeps the order
within each kind. There is no variable-count header: as in the HOL
semantics, unmentioned variables are unconstrained.

## Verified properties

| Theorem | Guarantee |
| --- | --- |
| `decode_encode_query` | For every query whose linear expressions have constant 0, the HOL encoder's canonical bytes decode to exactly that query. The decoder can express every such query and loses nothing. |
| `parse_rat_print_rat`, `parse_nat_print_nat` | Canonical integers and reduced fractions round-trip exactly. |
| `split_on_join`, `split_on_lines` | The canonical line and token layout is recovered exactly. |

The decoder is not trusted to match prose: it *is* the specification. The
round-trip theorem shows it is not degenerate. The encoder emits linear
statements, then bounds, then ReLUs, writing integers or reduced fractions.

[Exact_Query_Format_Examples.thy](../Isabelle/Exact_Query_Format_Examples.thy)
proves by `code_simp` that the header alone is the empty query, that all
statement forms and number spellings decode as stated, that `sat_rat_query`
has an exact model when read from bytes, and that the HOL encoder produces
the expected text. It proves rejection of: an empty file, a missing final
newline, a wrong header, an empty line, doubled or trailing spaces, wrong
case, wrong arity, a relation not matching its kind, an odd term list,
malformed variables, `1/0`, `1.`, `.5`, `1e3`, `+1`, `--1`, `1/2/3`,
`1.5/2`, a bare `-`, carriage returns, tabs and a non-ASCII byte. It also
proves that `1/2` and `1/4` decode differently.

## The ten captured starting queries as bytes

[exact_query_text.py](../Isabelle/tools/exact_query_text.py) is an untrusted
exporter mirroring the HOL encoder. It turns the saved
`marabou-plain-relu-query-v1` or `marabou-source-query-v1` snapshot of each
native scenario's starting query into `tests/fixtures/marabou/solver_<scenario>.mqx`
(90–361 bytes) and generates
[Imported_Marabou_Exact_Texts.thy](../Isabelle/Imported_Marabou_Exact_Texts.thy).
For each scenario that theory:

1. defines the file's bytes as a HOL list of numerals;
2. declares the file with `external_file`, so a changed file triggers a
   rebuild, and runs `Exact_Query_Text.check_file`, a build-time ML check
   that reads the file and fails unless it equals the list;
3. proves by `code_simp` that `decode_query` of the bytes is exactly the
   starting query of the existing replay theory;
4. restates that theory's result about the decoded bytes.

| Theorem | Statement |
| --- | --- |
| `solver_<scenario>_text_unsatisfiable` (nine UNSAT scenarios) | `decode_query solver_<scenario>_text = Some Q ⟹ unsatisfiable (embed_query Q)`. |
| `solver_relu_sat_text_model`, `..._satisfiable` | The exact native assignment is a real model of the query that the `relu_sat` bytes denote. |

For the four native-introduction scenarios the text is the query before any
ReLU auxiliary exists; for the other six it is the captured source query.
The check in step 2 was tested in a scratch session: a matching list passed
and a one-byte mismatch failed the build with
`Byte list differs from file probe.txt`.

[test_exact_query_text.py](../Isabelle/tests/test_exact_query_text.py) adds 10
tests: fixture and theory regeneration, literal/file identity and SHA-256
comments, the stated theorem shapes, canonical ASCII layout, agreement with
the HOL encoder example, exact fractions, value substitution changing the
text, rejection of unsupported JSON, and strict command-line use.

## Trust boundary after this step

Closed, for these files: the relation between a file's bytes and the HOL
query. The meaning of the bytes is `decode_query`; the bytes in the theory are
checked against the file during the build.

Still open:

* For these ten fixtures the C++ run did not read the files: the harness
  built its `InputQuery` in C++, and the `.mqx` files were exported afterwards
  from the captured JSON snapshots. The theorem is about what the files say,
  and each file says exactly the query that the replayed evidence refutes or
  satisfies. The later [query-file workflow](QUERY_FILE_WORKFLOW.md) does let
  the harness read a file itself.
* The Isabelle/ML file check and `external_file` are build infrastructure,
  not proof steps; they cannot create a theorem but are trusted to compare
  the right file.
* Network files, other input languages and the processed-query/JSON
  certificate import keep their earlier, unverified status.

That next step, a workflow in which the harness reads a `.mqx` file itself,
is now [available](QUERY_FILE_WORKFLOW.md).

## Reproduction

```sh
cd "/home/dusty/Desktop/Marabou Verification/Isabelle"
python3 tools/exact_query_text.py --fixtures tests/fixtures/marabou \
  --theory Imported_Marabou_Exact_Texts.thy
cd .. && isabelle build -D Isabelle
```

A single snapshot can be exported with
`python3 Isabelle/tools/exact_query_text.py --query Q.json --output Q.mqx`.
