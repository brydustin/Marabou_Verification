# Existing UAT sigmoid definition

The UAT development already defines the polymorphic logistic function in
[Sigmoid_Definition.thy](../../Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Sigmoid_Definition.thy),
in the `Sigmoid_Universal_Approximation` project:

```isabelle
definition sigmoid :: "'a::{real_normed_field,banach} ⇒ 'a" where
  "sigmoid x = exp x / (1 + exp x)"
```

The qualified constant is `Sigmoid_Definition.sigmoid`. A future sigmoid
query semantics should reuse its `real ⇒ real` instance. There is no reason
to introduce another logistic definition in this project.

The same file proves the real `sigmoid_alt_def`,
`sigmoid_pos`, `sigmoid_less_1`, `sigmoid_range`, `sigmoid_symmetry`,
`sigmoid_strictly_increasing` and `sigmoid_at_zero` facts.
[Sigmoid_Analytic.thy](../../Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/Sigmoid_Analytic.thy)
uses the same constant at type `complex` and connects it to the real instance
via `sigmoid_of_real`. Range and order facts are real-specific; the complex
denominator has zeros, so those claims must not be generalized indiscriminately.

Inspected on 2026-09-22:

* Directory: `/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation`.
* Repository HEAD: `7556df50622a2533d9e1bde4f60434eba4383318`.
* `Sigmoid_Definition.thy` is modified in that working tree. Its inspected
  SHA-256 is `850cb529c6767760dee033fc090fbb4a9f896b5fc118813b60d3eee3dc353ef3`;
  the definition above describes that working copy, not an asserted clean
  version at HEAD.
* Its session extends `Real_and_Complex_Analytic`. Reuse will need an explicit
  session dependency or an agreed extraction of the shared definition.

This milestone only reads and records that development. It does not modify
or rebuild UAT, add a dependency to `Marabou_Verification`, duplicate the
definition, or implement sigmoid certificate rules. The present checker
continues to support real linear arithmetic and ReLU.
