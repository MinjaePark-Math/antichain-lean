import Antichain.AlcoveDiscreteness
import Antichain.AlcoveFundamentalDomain
import Antichain.AlcoveCover

/-! All five actual alcove fields, derived directly from the type-A coordinates.
The legacy input record is inhabited by proofs, without an external premise. -/

noncomputable section

namespace Antichain

variable {d : ℕ} [NeZero d]

/-- The exact actual-tiles package, with every field proved inside Lean. -/
theorem humphreysAlcoveInput_direct (hd : 2 ≤ d) : HumphreysAlcoveInput d where
  covers := alcoveTile_covers_direct hd
  disjoint_interiors := alcoveTile_disjoint_interiors_direct hd
  locally_finite := alcoveTile_locallyFinite_direct d hd
  same_tile_map_unique := same_tile_map_unique_direct hd
  closed_alcove_orbit_representative_unique := closed_alcove_representative_unique_direct hd

end Antichain
