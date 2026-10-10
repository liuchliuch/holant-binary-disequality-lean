import Holant.Dihedral.SixPortBase.CrossingAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact support and projection counts in the original distinguished-pair
fibers. The row coefficients are actual sums, with parity excluding cancellation
between sectors before any cardinality is computed. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase.Crossing
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
set_option backward.isDefEq.respectTransparency false

abbrev Rows := PairWord → Mat
abbrev QuadWord := PairWord × PairWord

def rowSupport (F : Rows) : Finset QuadWord := by
  classical
  exact Finset.univ.biUnion (fun w => (binarySupport (F w)).image (fun y => (w,y)))

@[simp] theorem mem_rowSupport (F : Rows) (x : QuadWord) :
    x ∈ rowSupport F ↔ F x.1 x.2.1 x.2.2 ≠ 0 := by
  classical
  rcases x with ⟨w,y⟩
  simp [rowSupport]

theorem rowSupport_card (F : Rows) :
    (rowSupport F).card=∑ w,(binarySupport (F w)).card := by
  classical
  unfold rowSupport
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro w _
    apply Finset.card_image_of_injective
    intro y z h
    exact congrArg Prod.snd h
  · intro u _ v _ huv
    change Disjoint _ _
    rw [Finset.disjoint_left]
    rintro z hz hz'
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hz
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hz'
    exact huv (congrArg Prod.fst (ha.trans hb.symm))

@[simp] theorem binarySupport_zero : binarySupport (0 : Mat)=∅ := by
  classical
  ext x
  simp

theorem binarySupport_scale (c : Scalar) (A : Mat) :
    binarySupport (scale c A)=if c=0 then ∅ else binarySupport A := by
  classical
  ext x
  by_cases hc : c=0 <;> simp [hc,scale]

/-- A row sum uses the same original distinguished word on both summands. -/
def sumRows (U V : Mat) (A B : Rows) : Rows :=
  fun w a b => U w.1 w.2*A w a b+V w.1 w.2*B w a b

def ParitySupported (ε : Bool) (U : Mat) : Prop :=
  ∀ a b, b ≠ (a ^^ ε) → U a b=0

theorem paritySupported_monomial (ε : Bool) (w : Bool → Scalar) :
    ParitySupported ε (monomial ε w) := by
  intro a b h
  simp [monomial,h]

theorem opposite_parity_disjoint {ε : Bool} {U V : Mat}
    (hU : ParitySupported ε U) (hV : ParitySupported (!ε) V) (w : PairWord) :
    U w.1 w.2=0 ∨ V w.1 w.2=0 := by
  by_cases hu : w.2=(w.1 ^^ ε)
  · right
    apply hV
    rcases w with ⟨a,b⟩
    cases ε <;> cases a <;> cases b <;> simp_all
  · exact Or.inl (hU _ _ hu)

private theorem sumRows_card_general (U V : Mat) (A B : Rows) (n m : ℕ)
    (hd : ∀ w : PairWord,U w.1 w.2=0 ∨ V w.1 w.2=0)
    (hA : ∀ w,(binarySupport (A w)).card=n)
    (hB : ∀ w,(binarySupport (B w)).card=m) :
    (rowSupport (sumRows U V A B)).card=
      n*(binarySupport U).card+m*(binarySupport V).card := by
  classical
  rw [rowSupport_card]
  have row (w : PairWord) : (binarySupport (sumRows U V A B w)).card=
      (if U w.1 w.2 ≠ 0 then n else 0)+(if V w.1 w.2 ≠ 0 then m else 0) := by
    rcases hd w with hu|hv
    · have he : sumRows U V A B w=scale (V w.1 w.2) (B w) := by
        funext a b
        simp [sumRows,hu,scale]
      rw [he,binarySupport_scale]
      by_cases h : V w.1 w.2=0 <;> simp [hu,h,hB]
    · have he : sumRows U V A B w=scale (U w.1 w.2) (A w) := by
        funext a b
        simp [sumRows,hv,scale]
      rw [he,binarySupport_scale]
      by_cases h : U w.1 w.2=0 <;> simp [hv,h,hA]
  simp_rw [row]
  rw [Finset.sum_add_distrib]
  simp [binarySupport,Finset.sum_ite,Finset.filter_not,mul_comm]

private theorem sumRows_projection_general (U V : Mat) (A B : Rows)
    (hd : ∀ w : PairWord,U w.1 w.2=0 ∨ V w.1 w.2=0)
    (hA : ∀ w,(binarySupport (A w)).Nonempty)
    (hB : ∀ w,(binarySupport (B w)).Nonempty) :
    (rowSupport (sumRows U V A B)).image Prod.fst=binarySupport U ∪ binarySupport V := by
  classical
  ext w
  simp only [Finset.mem_image,mem_rowSupport,Finset.mem_union,mem_binarySupport]
  constructor
  · rintro ⟨⟨v,y⟩,hv,hvw⟩
    change v=w at hvw
    subst v
    by_contra hn
    push_neg at hn
    simp [sumRows,hn] at hv
  · intro h
    rcases hd w with hu|hv
    · have hv : V w.1 w.2 ≠ 0 := h.resolve_left (not_not_intro hu)
      obtain ⟨y,hy⟩ := hB w
      refine ⟨(w,y),?_,rfl⟩
      simpa [sumRows,hu] using mul_ne_zero hv ((mem_binarySupport _ _).mp hy)
    · have hu : U w.1 w.2 ≠ 0 := h.resolve_right (not_not_intro hv)
      obtain ⟨y,hy⟩ := hA w
      refine ⟨(w,y),?_,rfl⟩
      simpa [sumRows,hv] using mul_ne_zero hu ((mem_binarySupport _ _).mp hy)

theorem pp_card {ε : Bool} (U V : Mat) (A B : Rows)
    (hU : ParitySupported ε U) (hV : ParitySupported (!ε) V)
    (hA : ∀ w,IsMonomial (A w)) (hB : ∀ w,IsMonomial (B w)) :
    (rowSupport (sumRows U V A B)).card=
      2*((binarySupport U).card+(binarySupport V).card) := by
  rw [sumRows_card_general U V A B 2 2 (opposite_parity_disjoint hU hV)
    (fun w => monomial_support_card (hA w)) (fun w => monomial_support_card (hB w))]
  omega

theorem pc_card {ε : Bool} (U V : Mat) (A B : Rows)
    (hU : ParitySupported ε U) (hV : ParitySupported (!ε) V)
    (hVm : IsMonomial V)
    (hA : ∀ w,IsMonomial (A w)) (hB : ∀ w,IsPoint (B w)) :
    (rowSupport (sumRows U V A B)).card=2*(binarySupport U).card+2 := by
  rw [sumRows_card_general U V A B 2 1 (opposite_parity_disjoint hU hV)
    (fun w => monomial_support_card (hA w)) (fun w => point_support_card (hB w)),
    monomial_support_card hVm]

/-- The projected words are the original p-words, not newly chosen matching
coordinates on the resulting card. -/
theorem pc_projection_card {ε : Bool} (U V : Mat) (A B : Rows)
    (hU : ParitySupported ε U) (hV : ParitySupported (!ε) V)
    (hVm : IsMonomial V)
    (hA : ∀ w,IsMonomial (A w)) (hB : ∀ w,IsPoint (B w)) :
    ((rowSupport (sumRows U V A B)).image Prod.fst).card=(binarySupport U).card+2 := by
  rw [sumRows_projection_general U V A B (opposite_parity_disjoint hU hV)
    (fun w => Finset.card_pos.mp (by rw [monomial_support_card (hA w)]; omega))
    (fun w => Finset.card_pos.mp (by rw [point_support_card (hB w)]; omega)),
    Finset.card_union_of_disjoint,monomial_support_card hVm]
  rw [Finset.disjoint_left]
  intro w hu hv
  rcases opposite_parity_disjoint hU hV w with h|h
  · exact (mem_binarySupport _ _).mp hu h
  · exact (mem_binarySupport _ _).mp hv h

theorem pc_projection_three {ε : Bool} (U V : Mat) (A B : Rows)
    (hU : ParitySupported ε U) (hV : ParitySupported (!ε) V)
    (hVm : IsMonomial V)
    (hA : ∀ w,IsMonomial (A w)) (hB : ∀ w,IsPoint (B w))
    (h : (binarySupport U).card=1) :
    ((rowSupport (sumRows U V A B)).image Prod.fst).card=3 := by
  rw [pc_projection_card U V A B hU hV hVm hA hB,h]

end Holant.Dihedral.SixPortBase.Crossing
