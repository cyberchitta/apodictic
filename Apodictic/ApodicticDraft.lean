import ApodicticDraft.Money
import ApodicticDraft.Claims
import ApodicticDraft.Interest
import ApodicticDraft.Toy
import ApodicticDraft.NoPastMedium
import ApodicticDraft.Market
import ApodicticDraft.PriceControl
import ApodicticDraft.PriceControlToy
import ApodicticDraft.WeakRegress
import ApodicticDraft.CertaintySplitToy
import ApodicticDraft.KeptGiven
import ApodicticDraft.Satiation
import ApodicticDraft.NoMoneyLabel
import ApodicticDraft.ChristmasClubToy
import ApodicticDraft.ValuedAlike
import ApodicticDraft.RankedAlikeScoped

/-!
# ApodicticDraft

The draft library: unruled claims and provisional encodings live here
during a sprint, under the library's rules (constructive, linted,
claims documented in the three fields). It imports the trusted library;
nothing imports it — not the library, not the document — and it is not
a default target of the lake package. A ruling promotes a claim into
`Apodictic.Praxeology` and its theorems into the library.

Current content:

- T1, the pure time-preference theory of interest. S2–S5 are promoted
  (`Apodictic.PureInterest`, on the claim `MoreMoneyPreferredWhenSpent`
  and the vocabulary in `Apodictic.Money`). What stays here: S1 and
  Mises's route, and the rejected rivals, which are the merged
  certainty condition, the undated and stock-wide forms, and the
  availability reading (`ApodicticDraft.Interest`, on
  `MoreMoneyPreferred` in `ApodicticDraft.Claims`); the toy in
  `ApodicticDraft.Toy`.
- A medium with no past in the record (`ApodicticDraft.NoPastMedium`),
  a case against the regression theorem's premises. No claim.
- Price controls, link 1 (sprint 5): the vocabulary of a market of many
  agents in `ApodicticDraft.Market`, the static inequality in
  `ApodicticDraft.PriceControl`, the toy in
  `ApodicticDraft.PriceControlToy`. No claim.
- The regress from the weak first step (`ApodicticDraft.WeakRegress`),
  a rival to the library's `regress`. The unruled claim is in
  `ApodicticDraft.Claims`.
- Certainty named apart from purchasing power: promoted
  (`ClaimPays`, in `Apodictic.Money`). Each half failing alone, in
  `ApodicticDraft.CertaintySplitToy`. No claim.
- What `KeptServesOtherEnds` leaves of a good both traded and kept
  (`ApodicticDraft.KeptGiven`): it serves nothing. No claim.
- Non-satiation cut out of `MoreMoneyPreferred`
  (`ApodicticDraft.Satiation`): S3–S5 on the undated rival claim
  `MoreMoneyPreferredWhereDiffers`, in `ApodicticDraft.Claims`, with the
  library's condition `BuysMoreThanItsParts`.
- S3–S5 without the restriction to money
  (`ApodicticDraft.NoMoneyLabel`), on the rival claim
  `MorePreferredWhereDiffers`, in `ApodicticDraft.Claims`.
- A Christmas Club saver lending at a zero rate with every claim
  holding (`ApodicticDraft.ChristmasClubToy`): what fails is
  `SamePurchasingPower`. No claim.
- The "more money" claim dated at the spending, against the stock-wide
  condition `RankedAlikeNow` (`ApodicticDraft.ValuedAlike`), with a toy
  whose valuations change, which refutes the undated claim.
- The library's scoped `RankedAlikeNowOf` against the stock-wide rival
  (`ApodicticDraft.RankedAlikeScoped`). No claim.
-/
