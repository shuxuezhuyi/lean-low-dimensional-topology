# Explicit unproved statements

This directory holds concrete mathematical propositions whose proofs are still outstanding.
They are definitions of `Prop`, not axioms, and importing them supplies no proof.
Downstream theorems must take the required propositions as named explicit hypotheses.

Each statement must have a precise mathematical definition and a documented status,
reason for deferral, and actual downstream consumers. Conditional theorems are tracked
separately from unconditional proofs. A proposition equal to the desired conclusion
is not a substitute for proving a downstream result.

Keep implementation modules organized by subject. Use existing Mathlib objects and
actual maps, topologies, analytic structures, measures, and equations in the statements.
Do not replace a missing mathematical theory with arbitrary fields of type `Prop`.

The same-point Petersson integral proposition is proved for every original
coefficient representative, genuine deformed region and harmonic pair, without
assuming naturality or quantitative smoothing. The complete native and group
metric consumers now supply this proof internally and retain only quantitative
quasiconformal smoothing as an unresolved input. The older explicitly
parameterized family theorems and their recorded consumers remain available.

The independent `ThreeSphericalDiscs` proposition asks an ambient homeomorphism
of the fixed two-sphere to match two ordered triples of disjoint embedded closed
disc images. It remains unproved. The original three-end Nielsen-core
classification and hyperbolic-pants consumers receive it explicitly; the
complement-homeomorphism definition is documented separately from theorem
consumers. This does not settle prescribed boundary lengths or uniqueness.
