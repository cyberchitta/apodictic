import ApodicticDraft.Medium
import ApodicticDraft.Claims
import ApodicticDraft.Indirect
import ApodicticDraft.PartialDemands
import ApodicticDraft.Appraisal
import ApodicticDraft.Regress
import ApodicticDraft.PriorMoney
import ApodicticDraft.Toy

/-!
# ApodicticDraft

The draft library: unruled claims and provisional encodings live here
during a sprint, under the library's rules (constructive, linted,
claims documented in the three fields). It imports the trusted library;
nothing imports it — not the library, not the document — and it is not
a default target of the lake package. A ruling promotes a claim into
`Apodictic.Praxeology` and its theorems into the library.

Current content: T2, Mises's regression theorem, genetic claim
(sprint 2). The claim is in `ApodicticDraft.Claims`; the vocabulary in
`ApodicticDraft.Medium`.
-/
