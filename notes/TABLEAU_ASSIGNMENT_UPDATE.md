# Exact nonbasic tableau assignment update

`Tableau_State.thy` introduces a finite basic/nonbasic partition, solved
linear rows, row-consistency predicate, and a candidate valuation.
`Tableau_Assignment_Update.thy` defines an exact update to one nonbasic value
and adjusts each basic value by the coefficient of that variable in its row.
The coefficient helper sums duplicate terms, so the update is valid for the
existing list representation of linear expressions.

The central theorem is `update_nonbasic_preserves_rows`: if the old basic
assignments satisfy their rows, then after changing one nonbasic value and
adjusting the basics, all rows are still satisfied. Additional theorems show
that the state remains well-formed and that the selected nonbasic remains
within its bounds when its new value is within those bounds. The candidate
valuation consequently satisfies the solved-row equations.

This corresponds to the mathematics of Marabou's
`Tableau::setNonBasicAssignment(variable, value, true)` in
`upstream/Marabou/src/engine/Tableau.cpp:1484-1504`. The native method computes
`d = B^-1 A_j` in `computeChangeColumn` at lines 1452-1457 and updates each
basic assignment by subtracting `d * delta`. In the HOL row representation,
the coefficient is `-d`, so the same update is expressed as adding the row
coefficient times `delta`. The method is called in the lower/upper bound
update paths at lines 1785-1794 and 1800-1816.

This is an abstract solver-calculus theorem, not a refinement proof. Isabelle
does not establish that the C++ factorization returns the represented row
coefficient, model IEEE floating-point rounding or `FloatUtils` tolerances,
recompute basic-variable statuses, or prove cost-function cache invalidation.
Basic values can cross their bounds after the update; the native simplex
loop subsequently handles such violated basics. Only the selected nonbasic's
in-bound update is covered by the bound theorem.

The pivot has since been formalized (milestone 25, [TABLEAU_PIVOT.md](TABLEAU_PIVOT.md)).
The native operations are `Tableau::performPivot` (`Tableau.cpp:696`),
`Tableau::performDegeneratePivot` (803) and `Tableau::updateAssignmentForPivot`
(2345). A `pivot` near line 2130 exists only in the historical
`ReluplexCav2017/reluplex/Reluplex.h`, not in `Tableau.cpp`.
