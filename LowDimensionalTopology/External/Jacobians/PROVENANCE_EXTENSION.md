# Jacobians additions for the Teichmüller source extension

Eleven modules extend the original 183-module selection. The base selection
keeps its own `UPSTREAM.json` and adaptation records; its original sources,
license and provenance are retained. They come from the
same [fixed QC archive](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization/tree/1c0d5473c020b66ed5106331a38a61536760b9b2), which records
`rkirov/jacobian-claude@73212f7ef2bb46a7884710b18fe1e18b8509e3e5`
as its upstream. The exact archive hashes, original manifest records and local
module correspondence are in
`../LiZhongQC/EXTENSION_UPSTREAM.json`.

Original copyright headers and the existing complete Apache-2.0 and secondary
MIT license records are retained. Historical vendor-reported hashes are retained as historical records. Separately,
the eleven fixed primary-upstream Git raw hashes and blob identifiers have now
been independently verified and are recorded in the extension manifest. Source `ProjectiveLine`
consumers explicitly open `Jacobians.RiemannSphere`, preserving its original
two-chart atlas separately from the project's canonical sphere structure.

Eight additions have recorded current-public-API or proposition-instance-style
adaptations. Both initial preparation and current hashes are retained in the
extension manifest. No Lean/LSP/build or compiled axiom audit has yet been run
for these additions.
