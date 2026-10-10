import Holant.Proofs.Reductions.GeneralExtraction.Nonvanishing
import Mathlib.Tactic.Positivity


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralCarrierExistence
open scoped BigOperators
open NamedContraction SupportDescent SupportCaps NativeCopies BinaryCarrier Nonvanishing
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction

variable {K : Type*} [Field K] {n m : ℕ}

def MixedSupport (F : SignatureFamily K) : Prop :=
  ∀ b : Bool, ∃ n : ℕ, ∃ f : Signature K n,
    (⟨n, f⟩ : AnySignature K) ∈ F ∧ ∃ x, f x ≠ 0 ∧ 0 < balance b x

/-- This records a physical graph with literal occurrences. In particular
`factor_present` rules out satisfying existence by the empty unit graph. -/
structure Witness (F : SignatureFamily K) (f : Signature K n) where
  graph : Network K 0
  factor : Fin graph.shape.vertices → Bool
  factor_label : ∀ v, factor v = true →
    (⟨graph.shape.arity v, graph.vertex v⟩ : AnySignature K) = ⟨n, f⟩
  background_label : ∀ v, factor v = false →
    (⟨graph.shape.arity v, graph.vertex v⟩ : AnySignature K) ∈ F
  factor_present : ∃ v, factor v = true
  native : Native graph
  nonzero : graph.denote Fin.elim0 ≠ 0

theorem purePin_tensor (c d : K) (b : Bool) :
    Signature.tensor (purePin c b n) (purePin d b m) = purePin (c * d) b (n + m) := by
  funext x
  have he : x = (fun _ => b) ↔
      (fun i => x (Fin.castAdd m i)) = (fun _ => b) ∧
      (fun i => x (Fin.natAdd n i)) = (fun _ => b) := by
    constructor
    · intro h; simp [h]
    · rintro ⟨hL, hR⟩
      funext i
      refine Fin.addCases (fun i => congrFun hL i) (fun i => congrFun hR i) i
  by_cases hL : (fun i => x (Fin.castAdd m i)) = (fun _ => b) <;>
    by_cases hR : (fun i => x (Fin.natAdd n i)) = (fun _ => b) <;>
    simp [Signature.tensor_apply, purePin, he, hL, hR]

theorem copies_pin (N : Network K n) (c : K) (b : Bool)
    (h : N.denote = purePin c b n) (r : ℕ) :
    (copies N r).denote = purePin (c ^ r) b (copyArity n r) := by
  induction r with
  | zero =>
    funext x
    have hx : x = fun _ => b := by funext i; exact Fin.elim0 i
    simp [copies, purePin, hx, Network.denote_empty]
  | succ r ih =>
    rw [copies, Network.denote_tensor, h, ih, purePin_tensor]
    simpa only [copyArity, pow_succ, mul_comm]

theorem copies_constant (N : Network K n) (b : Bool) (r : ℕ) :
    (copies N r).denote (fun _ => b) = N.denote (fun _ => b) ^ r := by
  induction r <;>
    simp [copies, Network.denote_empty, Network.denote_tensor, Signature.tensor_apply, *, pow_succ, mul_comm]

theorem native_constant (b : Bool) (y : Fin n → Bool) :
    (∏ i, Signature.disequality (K := K) b (y i)) =
      if y = (fun _ => !b) then 1 else 0 := by
  have he : ∀ u, Signature.disequality (K := K) b u = if u = !b then 1 else 0 := by
    intro u
    cases b <;> cases u <;> rfl
  simp only [he, Fintype.prod_boole, ← funext_iff]

theorem glue_pin (L R : Network K n) (c : K) (b : Bool)
    (hL : L.denote = purePin c b n) :
    (L.glue R (fun _ => Signature.disequality)).denote Fin.elim0 =
      c * R.denote (fun _ => !b) := by
  rw [Network.denote_glue]
  simp [hL, purePin, native_constant]

/-- Transpose copy/port indices. This gives the original proof's complete
bipartite incidence, not a numerical tensor identification. -/
def gridOrder (r d : ℕ) : Fin (copyArity d r) ≃ Fin (copyArity r d) :=
  (finCongr (copyArity_eq d r)).trans
    (finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans
      (finProdFinEquiv.trans (finCongr (copyArity_eq r d)).symm)))

/-- Build the final carrier from actual one-copy loop descendants, without
adding the descendant signatures as target-family resources. -/
def gridWitness (F : SignatureFamily K) (f : Signature K n)
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) (b : Bool) (c : K) (hc : c ≠ 0)
    (P : Network K r) (hPU : Uses P {⟨n, f⟩}) (hPN : Native P)
    (hPv : P.shape.vertices = 1) (hP : P.denote = purePin c b r)
    (T : Network K d) (hTU : Uses T F) (hTN : Native T)
    (hT : T.denote (fun _ => !b) ≠ 0) : Witness F f := by
  let L := copies P d
  let R := reboundary (copies T r) (gridOrder r d)
  let C := L.glue R (fun _ => Signature.disequality)
  let mark : Fin C.shape.vertices → Bool := fun v =>
    match (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
    | .inl _ => true
    | .inr _ => false
  have hLU : Uses L {⟨n, f⟩} := copies_uses _ P hPU d
  have hRU : Uses R F := copies_uses F T hTU r
  refine ⟨C, mark, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    change (⟨_, (Network.glueFinite L R (fun _ => Signature.disequality)).vertex
      ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ : AnySignature K) = _
    cases he : (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
    | inl v => exact Set.mem_singleton_iff.mp (hLU v)
    | inr v => simp [mark, he] at hv
  · intro v hv
    change (⟨_, (Network.glueFinite L R (fun _ => Signature.disequality)).vertex
      ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ : AnySignature K) ∈ F
    cases he : (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
    | inl v => simp [mark, he] at hv
    | inr v => exact hRU v
  · have hLv : 0 < L.shape.vertices := by simpa [L, copies_vertices, hPv] using hd
    refine ⟨(Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)) (.inl ⟨0, hLv⟩), ?_⟩
    simp [mark]
  · exact glue_native L R (copies_native P hPN d) (copies_native T hTN r)
  · have he : C.denote Fin.elim0 = c ^ d * T.denote (fun _ => !b) ^ r := by
      rw [glue_pin L R (c ^ d) b (copies_pin P c b hP d)]
      rw [reboundary_denote, copies_constant]
    rw [he]
    exact mul_ne_zero (pow_ne_zero d hc) (pow_ne_zero r hT)

theorem witness_of_strict (F : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (hF : MixedSupport F) (f : Signature K n) (hf : f ≠ 0)
    (b : Bool) (hs : StrictSide b f) : Nonempty (Witness F f) := by
  obtain ⟨r, hr, c, hc, P, hPU, hPN, hPv, hP⟩ := strict_side_pin htwo b f hf hs
  obtain ⟨d₀, t, ht, x, hx, hxb⟩ := hF (!b)
  obtain ⟨d, hd, T, hTU, hTN, _, _, hT⟩ := support_cap htwo (!b) t x hx hxb
  have hTU' : Uses T F := by
    intro v
    have he := Set.mem_singleton_iff.mp (hTU v)
    rw [he]
    exact ht
  exact ⟨gridWitness F f hr hd b c hc P hPU hPN hPv hP T hTU' hTN hT⟩

/-- General carrier existence, with a positive number of f occurrences and
all remaining occurrences from the ORIGINAL retained family. This closes
the mathematical existence branch, not the encoded tensor-power reduction. -/
theorem factor_carrier (F : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (hF : MixedSupport F) (hn : 0 < n) (f : Signature K n) (hf : f ≠ 0) :
    Nonempty (Witness F f) := by
  by_cases hfalse : StrictSide false f
  · exact witness_of_strict F htwo hF f hf false hfalse
  by_cases htrue : StrictSide true f
  · exact witness_of_strict F htwo hF f hf true htrue
  obtain ⟨C, hU, hN, hV, hC⟩ := carrier_of_not_strict htwo hn f hfalse htrue
  refine ⟨⟨C, fun _ => true, ?_, ?_, ⟨⟨0, hV⟩, rfl⟩, hN, hC⟩⟩
  · intro v _
    exact Set.mem_singleton_iff.mp (hU v)
  · intro v hv
    cases hv

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralCarrierExistence
