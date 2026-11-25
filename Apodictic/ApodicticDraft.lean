import ApodicticDraft.Money
import ApodicticDraft.Claims
import ApodicticDraft.Interest
import ApodicticDraft.Toy
import ApodicticDraft.NoPastMedium
import ApodicticDraft.Market
import ApodicticDraft.PriceControl
import ApodicticDraft.PriceControlToy
import ApodicticDraft.WeakRegress
import ApodicticDraft.CertaintySplit

/-!
# ApodicticDraft

The draft library: unruled claims and provisional encodings live here
during a sprint, under the library's rules (constructive, linted,
claims documented in the three fields). It imports the trusted library;
nothing imports it — not the library, not the document — and it is not
a default target of the lake package. A ruling promotes a claim into
`Apodictic.Praxeology` and its theorems into the library.

Current content:

- T1, the pure time-preference theory of interest (sprint 3). The
  unruled claim is in `ApodicticDraft.Claims`; the vocabulary in
  `ApodicticDraft.Money`; the toy in `ApodicticDraft.Toy`.
- A medium with no past in the record (`ApodicticDraft.NoPastMedium`),
  a case against the regression theorem's premises. No claim.
- Price controls, link 1 (sprint 5): the vocabulary of a market of many
  agents in `ApodicticDraft.Market`, the static inequality in
  `ApodicticDraft.PriceControl`, the toy in
  `ApodicticDraft.PriceControlToy`. No claim.
- The regress from the weak first step (`ApodicticDraft.WeakRegress`),
  a rival to the library's `regress`. The unruled claim is in
  `ApodicticDraft.Claims`.
- Certainty named apart from purchasing power
  (`ApodicticDraft.CertaintySplit`), a rival to T1's merged condition.
  No claim.
-/
