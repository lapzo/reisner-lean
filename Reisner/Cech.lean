module

public import Reisner.Cech.Basic
public import Reisner.Cech.Indices
public import Reisner.Cech.LinkComparison
public import Reisner.Cech.ShiftedLink
public import Reisner.Cech.UniformLink
public import Reisner.Cech.LinkHomology
public import Reisner.Cech.Purity
public import Reisner.Cech.ExtComparison
public import Reisner.Cech.LocalizedExt
public import Reisner.Cech.FaceRingLinear

/-!
Public compatibility module for the extended Cech development. The proofs
are organized by dependency in `Reisner.Cech.Basic`, `Indices`,
`LinkComparison`, and `ShiftedLink`. Importing `Reisner.Cech` continues to
expose the complete API, including the cutoff equivalence between total Čech
cohomology vanishing and reduced cohomology vanishing on links.
For field coefficients, it also exposes the equivalent link-homology
vanishing criterion in face-cardinality degrees. `Reisner.Cech.LocalizedExt`
records derived Ext-stage and Ext-colimit vanishing against nonempty
face-ring localization targets.
-/
