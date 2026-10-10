import Holant.Dihedral.SixPortBase.CrossingTopology
import Holant.Dihedral.SixPortBase.CrossingCounts

/-! The crossing support conclusions for arbitrary literal matching products
on the original four residual ports, including exact coefficient contractions. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase.Crossing
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
set_option backward.isDefEq.respectTransparency false

abbrev Residual := Signature Scalar 4

def residualSupport (F : Residual) : Finset (Fin 4 → Bool) := by
  classical
  exact Finset.univ.filter (fun x => F x ≠ 0)

@[simp] theorem mem_residualSupport (F : Residual) (x : Fin 4 → Bool) :
    x ∈ residualSupport F ↔ F x ≠ 0 := by
  classical
  simp [residualSupport]

def survivorWord (c : (Bool × Bool) ≃ Fin 4) (u v : Bool) : Fin 4 → Bool :=
  fun i => if (c.symm i).2 then v else u

@[simp] theorem survivorWord_apply (c : (Bool × Bool) ≃ Fin 4)
    (a b u v : Bool) : survivorWord c u v (c (a,b))=if b then v else u := by
  simp [survivorWord]

/-- A literal two-port contraction; the two output arguments belong to the
original survivors c(true,false) and c(true,true). -/
def originalContract (c : (Bool × Bool) ≃ Fin 4) (γ : Bool) (F : Residual) : Mat :=
  fun u v => ∑ i : Bool, ∑ j : Bool, M γ 1 i j * F
    (insertPair (c (false,false)) (c (false,true)) i j (survivorWord c u v))

theorem oriented_monomial (b : Bool) {A : Mat} (hA : IsMonomial A) :
    IsMonomial (orientMatrix b A) := by
  cases b
  · exact hA
  · exact hA.transpose

theorem oriented_point (b : Bool) {A : Mat} (hA : IsPoint A) :
    IsPoint (orientMatrix b A) := by
  cases b
  · exact hA
  · exact hA.transpose

theorem point_scale {A : Mat} (hA : IsPoint A) {κ : Scalar} (hκ : κ ≠ 0) :
    IsPoint (scale κ A) := by
  obtain ⟨r,s,d,hd,rfl⟩ := hA
  refine ⟨r,s,κ*d,mul_ne_zero hκ hd,?_⟩
  funext u v
  simp [scale,point,mul_ite]

/-- This equation retains both original factor orientations, the original
common deletion chart and the exact nonzero product scalar. -/
theorem crossed_original_form {p : (Fin 2 × Bool) ≃ Fin 4}
    {c : (Bool × Bool) ≃ Fin 4} (h : Crossed p c)
    (A : Fin 2 → Mat) (κ : Scalar) (γ : Bool) :
    ∃ e f : Fin 2, e ≠ f ∧ ∃ b d s : Bool,
      originalContract c γ (productValue p A κ)=
        scale κ (orientMatrix s (contract γ (orientMatrix (!b) (A e))
          (orientMatrix d (A f)))) := by
  obtain ⟨e,f,hef,b,d,s,hc⟩ := h.close_product A κ
  refine ⟨e,f,hef,b,d,s,?_⟩
  funext u v
  have hh := hc (M γ 1) (survivorWord c u v)
  change originalContract c γ (productValue p A κ) u v = _ at hh
  rw [hh]
  cases s <;> simp [scale,orientMatrix,Kernel.transpose,contract]

theorem original_contract_monomial {p : (Fin 2 × Bool) ≃ Fin 4}
    {c : (Bool × Bool) ≃ Fin 4} (h : Crossed p c)
    (A : Fin 2 → Mat) (κ : Scalar) (hA : ∀ e,IsMonomial (A e))
    (hκ : κ ≠ 0) (γ : Bool) :
    IsMonomial (originalContract c γ (productValue p A κ)) := by
  obtain ⟨e,f,_,b,d,s,he⟩ := crossed_original_form h A κ γ
  rw [he]
  exact (oriented_monomial s (contract_isMonomial γ
    (oriented_monomial (!b) (hA e)) (oriented_monomial d (hA f)))).scale hκ

def OnePointProduct (A : Fin 2 → Mat) : Prop :=
  (IsMonomial (A 0) ∧ IsPoint (A 1)) ∨ (IsPoint (A 0) ∧ IsMonomial (A 1))

private theorem onePoint_pair (A : Fin 2 → Mat) (hA : OnePointProduct A)
    (e f : Fin 2) (hef : e ≠ f) :
    (IsMonomial (A e) ∧ IsPoint (A f)) ∨ (IsPoint (A e) ∧ IsMonomial (A f)) := by
  fin_cases e <;> fin_cases f <;> simp_all [OnePointProduct,and_comm,or_comm]

theorem original_contract_point {p : (Fin 2 × Bool) ≃ Fin 4}
    {c : (Bool × Bool) ≃ Fin 4} (h : Crossed p c)
    (A : Fin 2 → Mat) (κ : Scalar) (hA : OnePointProduct A)
    (hκ : κ ≠ 0) (γ : Bool) :
    IsPoint (originalContract c γ (productValue p A κ)) := by
  obtain ⟨e,f,hef,b,d,s,he⟩ := crossed_original_form h A κ γ
  rw [he]
  apply point_scale _ hκ
  apply oriented_point
  rcases onePoint_pair A hA e f hef with ⟨he,hf⟩|⟨he,hf⟩
  · exact contract_point_right γ (oriented_monomial _ he) (oriented_point _ hf)
  · exact contract_point_left γ (oriented_point _ he) (oriented_monomial _ hf)

/-- The support description is derived from all actual factor coefficients;
there are no assumed support or cardinality inputs. -/
theorem product_support_words (p : (Fin 2 × Bool) ≃ Fin 4)
    (A : Fin 2 → Mat) (κ : Scalar) (hA : ∀ e,IsMonomial (A e)) (hκ : κ ≠ 0) :
    ∃ α : Fin 2 → Bool,residualSupport (productValue p A κ)=
      Finset.univ.image (SectorRuling.matchingWord p α) := by
  classical
  choose α w hw he using hA
  refine ⟨α,?_⟩
  have hs (x : Fin 4 → Bool) : productValue p A κ x ≠ 0 ↔
      ∀ e,x (p (e,true))=(x (p (e,false)) ^^ α e) := by
    simp only [productValue,mul_ne_zero_iff,hκ,true_and,
      Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const]
    simp [he,monomial,hw,hκ]
  ext x
  rw [mem_residualSupport,hs]
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro hx
    refine ⟨fun e => x (p (e,false)),?_⟩
    funext i
    obtain ⟨⟨e,b⟩,rfl⟩ := p.surjective i
    cases b
    · simp [SectorRuling.matchingWord]
    · simpa [SectorRuling.matchingWord] using (hx e).symm
  · rintro ⟨z,rfl⟩ e
    simp [SectorRuling.matchingWord]

theorem product_projection_two_or_four (p : (Fin 2 × Bool) ≃ Fin 4)
    (A : Fin 2 → Mat) (κ : Scalar) (hA : ∀ e,IsMonomial (A e)) (hκ : κ ≠ 0)
    (u v : Fin 4) (huv : u ≠ v) :
    ((residualSupport (productValue p A κ)).image (fun x => (x u,x v))).card=2 ∨
    ((residualSupport (productValue p A κ)).image (fun x => (x u,x v))).card=4 := by
  obtain ⟨α,hα⟩ := product_support_words p A κ hA hκ
  rw [hα,Finset.image_image]
  exact matchingWord_projection_two_or_four p α u v huv

theorem product_support_four (p : (Fin 2 × Bool) ≃ Fin 4)
    (A : Fin 2 → Mat) (κ : Scalar) (hA : ∀ e,IsMonomial (A e)) (hκ : κ ≠ 0) :
    (residualSupport (productValue p A κ)).card=4 := by
  classical
  obtain ⟨α,hα⟩ := product_support_words p A κ hA hκ
  rw [hα,Finset.card_image_of_injective]
  · decide
  · intro z w h
    funext e
    have he := congrFun h (p (e,false))
    simpa [SectorRuling.matchingWord] using he

end Holant.Dihedral.SixPortBase.Crossing
