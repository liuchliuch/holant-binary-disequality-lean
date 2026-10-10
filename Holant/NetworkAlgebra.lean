import Holant.Network

/-! Exact scalar accounting and interpretation of network coefficients. -/

namespace Holant.Network

variable {K L : Type*} [CommSemiring K] [CommSemiring L] {n : ℕ}

/-- Keep explicit one-factor-per-vertex normalization data. -/
def scaleVertices (N : Network K n) (c : Fin N.shape.vertices → K) : Network K n where
  shape := N.shape
  vertex := fun v x => c v * N.vertex v x
  edge := N.edge

/-- Independent edge scalars are also retained once per edge. -/
def scaleEdges (N : Network K n) (c : Fin N.shape.edges → K) : Network K n where
  shape := N.shape
  vertex := N.vertex
  edge := fun e a b => c e * N.edge e a b

theorem denote_scaleVertices (N : Network K n) (c : Fin N.shape.vertices → K)
    (x : Fin n → Bool) :
    (N.scaleVertices c).denote x = (∏ v, c v) * N.denote x := by
  simp only [denote, scaleVertices, Finset.prod_mul_distrib, mul_assoc, Finset.mul_sum]
  rfl

theorem denote_scaleEdges (N : Network K n) (c : Fin N.shape.edges → K)
    (x : Fin n → Bool) :
    (N.scaleEdges c).denote x = (∏ e, c e) * N.denote x := by
  simp only [denote, scaleEdges, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ac_rfl

/-- Interpret every coefficient by a semiring homomorphism, preserving incidence. -/
def map (φ : K →+* L) (N : Network K n) : Network L n where
  shape := N.shape
  vertex := fun v x => φ (N.vertex v x)
  edge := fun e a b => φ (N.edge e a b)

/-- Semantic bridge for any exact coefficient interpretation. It asserts no runtime bound. -/
theorem denote_map (φ : K →+* L) (N : Network K n) (x : Fin n → Bool) :
    (N.map φ).denote x = φ (N.denote x) := by
  simp [denote, map, map_sum, map_prod]
  rfl

end Holant.Network
