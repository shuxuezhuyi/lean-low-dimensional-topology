# Path perturbation and sphere topology

The three path modules are adapted from **Rado Kirov**,
[LeanPool/lean-pool](https://github.com/LeanPool/lean-pool), commit
`86da5902e640ceb44e53f88c4a04f870dc062126`, under Apache 2.0.
Original copyright and author notices are retained in every source; the
complete license is [../LICENSE](../LICENSE). `UPSTREAM.json` records the
exact original and local SHA-256 of every copied file and its modifications.

`LowDimensionalTopology/Geometry/Surfaces/Riemann/RiemannSphereTopology.lean` adapts the polar-cap and path-perturbation
proof in `LeanPool/JacobianDiffgeo/SphereTopology/SimplyConnectedP1.lean`, with
its original notice retained. It uses this project's existing genuine sphere
atlas and reciprocal homeomorphism, avoiding a second sphere atlas and five
unneeded upstream modules. Its additional compactness and genus-zero conformal
consequences use the separately proved general uniformization theorem.

The resulting proof gives actual simple connectivity of `OnePoint ℂ`, then
proves that an original Riemann surface with the topology of the literal
Euclidean unit two-sphere is conformally the genuine Riemann sphere. It does
not establish the genus-one or higher-genus cases.
