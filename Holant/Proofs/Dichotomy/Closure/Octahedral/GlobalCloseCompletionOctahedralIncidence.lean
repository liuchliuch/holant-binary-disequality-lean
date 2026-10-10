import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralAction

/-! Coefficient extraction from the preserved marked-octahedral proof. The internally produced permutation preserves every
literal root secant, including its complete finite intersection and size.
This proves incidence automorphism, not the 1152-element classification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open scoped BigOperators Matrix

theorem mulVec_span_pair_iff (A : End) (hd : A.det ≠ 0) (u v w : V) :
    A *ᵥ w ∈ Submodule.span ℂ ({A *ᵥ u,A *ᵥ v} : Set V) ↔
      w ∈ Submodule.span ℂ ({u,v} : Set V) := by
  constructor
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨a,b,?_⟩
    apply Matrix.mulVec_injective_of_det_ne_zero hd
    simpa only [Matrix.mulVec_add,Matrix.mulVec_smul] using he
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨a,b,?_⟩
    simpa only [Matrix.mulVec_add,Matrix.mulVec_smul] using congrArg A.mulVec he

theorem scaled_span_pair_iff (u v w : V) (a b c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    c • w ∈ Submodule.span ℂ ({a • u,b • v} : Set V) ↔
      w ∈ Submodule.span ℂ ({u,v} : Set V) := by
  constructor
  · intro h
    obtain ⟨x,y,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨c⁻¹*x*a,c⁻¹*y*b,?_⟩
    have hh := congrArg (fun z : V => c⁻¹ • z) he
    simpa only [smul_add,smul_smul,inv_mul_cancel₀ hc,one_smul,mul_assoc] using hh
  · intro h
    obtain ⟨x,y,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨c*x*a⁻¹,c*y*b⁻¹,?_⟩
    have hh := congrArg (fun z : V => c • z) he
    simpa only [smul_add,smul_smul,mul_assoc,inv_mul_cancel₀ ha,
      inv_mul_cancel₀ hb,mul_one] using hh

abbrev IncidencePermutation (f : Form) :=
  {σ : Equiv.Perm (Fin 24) // ∀ i j k : Fin 24,
    point f (σ k) ∈ Submodule.span ℂ ({point f (σ i),point f (σ j)} : Set V) ↔
      point f k ∈ Submodule.span ℂ ({point f i,point f j} : Set V)}

theorem RootAction.incidence {f : Form} {A : End}
    (p : RootAction f A) (hd : A.det ≠ 0) (i j k : Fin 24) :
    point f (p.perm k) ∈
        Submodule.span ℂ ({point f (p.perm i),point f (p.perm j)} : Set V) ↔
      point f k ∈ Submodule.span ℂ ({point f i,point f j} : Set V) := by
  have h := mulVec_span_pair_iff A hd (point f i) (point f j) (point f k)
  rw [p.image_eq i,p.image_eq j,p.image_eq k] at h
  exact (scaled_span_pair_iff _ _ _ _ _ _ (p.scale_ne_zero i)
    (p.scale_ne_zero j) (p.scale_ne_zero k)).symm.trans h

def RootAction.incidencePermutation {f : Form} {A : End}
    (p : RootAction f A) (hd : A.det ≠ 0) : IncidencePermutation f :=
  ⟨p.perm,p.incidence hd⟩

def secant (f : Form) (i j : Fin 24) : Finset (Fin 24) := by
  classical
  exact Finset.univ.filter fun k =>
    point f k ∈ Submodule.span ℂ ({point f i,point f j} : Set V)

@[simp] theorem mem_secant (f : Form) (i j k : Fin 24) :
    k ∈ secant f i j ↔ point f k ∈ Submodule.span ℂ ({point f i,point f j} : Set V) := by
  classical
  simp only [secant,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Exact equality of finite root intersections, not just preservation of
three named points or a promised rich-line count. -/
theorem RootAction.map_secant {f : Form} {A : End}
    (p : RootAction f A) (hd : A.det ≠ 0) (i j : Fin 24) :
    (secant f i j).map p.perm.toEmbedding = secant f (p.perm i) (p.perm j) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨m,hm,rfl⟩ := Finset.mem_map.mp hk
    exact (mem_secant _ _ _ _).mpr
      ((p.incidence hd i j m).mpr ((mem_secant _ _ _ _).mp hm))
  · intro hk
    refine Finset.mem_map.mpr ⟨p.perm.symm k,?_,p.perm.apply_symm_apply k⟩
    apply (mem_secant _ _ _ _).mpr
    apply (p.incidence hd i j (p.perm.symm k)).mp
    simpa only [p.perm.apply_symm_apply] using (mem_secant _ _ _ _).mp hk

theorem RootAction.secant_card {f : Form} {A : End}
    (p : RootAction f A) (hd : A.det ≠ 0) (i j : Fin 24) :
    (secant f (p.perm i) (p.perm j)).card = (secant f i j).card := by
  rw [←p.map_secant hd i j,Finset.card_map]

structure TwoSidedAction (f : Form) (A : End) where
  rank_four : A.rank = 4
  det_ne_zero : A.det ≠ 0
  forward : RootAction f A
  adjoint : RootAction f (sharp A)
  forwardIncidence : IncidencePermutation f
  forward_perm_eq : forwardIncidence.val = forward.perm
  adjointIncidence : IncidencePermutation f
  adjoint_perm_eq : adjointIncidence.val = adjoint.perm
  inverse_safe : OneSided (Roots f) A⁻¹
  adjoint_inverse_safe : OneSided (Roots f) (sharp A)⁻¹

/-- Both root permutations come from the actual pair map and its actual
Frobenius adjoint. No second independently supplied operator is accepted. -/
def twoSidedAction (f : Form) (A : End) (hr : A.rank = 4)
    (h : TwoSided (Roots f) A) : TwoSidedAction f A := by
  have hd := (rank_four_iff_det_ne_zero A).mp hr
  have hs : (sharp A).rank = 4 := (rank_sharp A).trans hr
  have hsd := (rank_four_iff_det_ne_zero (sharp A)).mp hs
  let p := rootAction f A hd h.1
  let q := rootAction f (sharp A) hsd h.2
  exact ⟨hr,hd,p,q,p.incidencePermutation hd,rfl,
    q.incidencePermutation hsd,rfl,inverse_oneSided f A hd h.1,
    inverse_oneSided f (sharp A) hsd h.2⟩

/-- Ranks two and three retain their mathematical residuals. Full rank
contains the newly produced automorphism of the literal 24-root set. -/
inductive RankEvent (f : Form) (A : End) : Type
  | rankTwo (rank_eq : A.rank = 2)
  | rankThree (rank_eq : A.rank = 3)
  | rankFour (action : TwoSidedAction f A)

/-- The only disjunction is the existing proved possible-ranks receipt.
Actual by_cases produces the Type-valued branch; Or is eliminated only
into the proof of rank=4. No desired branch is supplied by a caller. -/
def rankEvent (f : Form) (A : End) (h : TwoSided (Roots f) A)
    (possible : A.rank = 2 ∨ A.rank = 3 ∨ A.rank = 4) : RankEvent f A := by
  classical
  by_cases htwo : A.rank = 2
  · exact .rankTwo htwo
  by_cases hthree : A.rank = 3
  · exact .rankThree hthree
  have hfour : A.rank = 4 := (possible.resolve_left htwo).resolve_left hthree
  exact .rankFour (twoSidedAction f A hfour h)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
