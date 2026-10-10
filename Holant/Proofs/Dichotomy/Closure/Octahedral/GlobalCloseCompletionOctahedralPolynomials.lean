import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralConditions
import Mathlib.Algebra.MvPolynomial.Eval

/-! Coefficient extraction from the preserved marked-octahedral proof. Exact elimination of the image scalar and image-index
disjunction. These are polynomial equations in the sixteen entries of the
actual pair map, for arbitrary complex input matrices, not a candidate list.
The equations do not assert the S4 rank/orbit classification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open scoped BigOperators Matrix

def minor (v w : V) (a b : Fin 4) : ℂ := v a*w b-v b*w a
def LineCone (v w : V) : Prop := ∀ a b : Fin 4, minor v w a b = 0

/-- The zero vector is intentionally included; no free nonzero scalar is
supplied as an input. The pivot comes from the actual nonzero root vector. -/
theorem lineCone_iff (v w : V) (hw : w ≠ 0) :
    LineCone v w ↔ ∃ c : ℂ, v = c • w := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hw
    refine ⟨v i/w i,?_⟩
    ext j
    have hh : v j*w i = v i*w j := sub_eq_zero.mp (h j i)
    change v j = (v i/w i)*w j
    rw [div_mul_eq_mul_div,←hh,mul_div_cancel_right₀ _ hi]
  · rintro ⟨c,rfl⟩ a b
    simp only [minor,Pi.smul_apply,smul_eq_mul]
    ring

theorem vectorSafe_iff_lineCone (f : Form) (v : V) :
    VectorSafe f v ↔ ∃ j : Fin 24, LineCone v (point f j) := by
  constructor
  · rintro (rfl | hv)
    · exact ⟨0,by intro a b; simp [minor]⟩
    · obtain ⟨j,c,hc,he⟩ := (roots_iff f v).mp hv
      exact ⟨j,(lineCone_iff v _ (point_ne_zero f j)).mpr ⟨c,he⟩⟩
  · rintro ⟨j,hj⟩
    obtain ⟨c,he⟩ := (lineCone_iff v _ (point_ne_zero f j)).mp hj
    by_cases hc : c = 0
    · exact Or.inl (by simpa only [hc,zero_smul] using he)
    · exact Or.inr ((roots_iff f v).mpr ⟨j,c,hc,he⟩)

abbrev MinorChoice := Fin 24 → Fin 4 × Fin 4

/-- A finite union of lines is cut out exactly by products of one selected
minor per possible target line. This proves completeness of the equations,
without choosing target roots as classifier inputs. -/
theorem exists_lineCone_iff_products (f : Form) (v : V) :
    (∃ j : Fin 24, LineCone v (point f j)) ↔
      ∀ d : MinorChoice, (∏ j : Fin 24, minor v (point f j) (d j).1 (d j).2) = 0 := by
  classical
  constructor
  · rintro ⟨j,hj⟩ d
    exact Finset.prod_eq_zero (Finset.mem_univ j) (hj (d j).1 (d j).2)
  · intro h
    by_contra hn
    have hf : ∀ j : Fin 24, ∃ ab : Fin 4 × Fin 4,
        minor v (point f j) ab.1 ab.2 ≠ 0 := by
      intro j
      by_contra hh
      push_neg at hh
      exact hn ⟨j,fun a b => hh (a,b)⟩
    choose d hd using hf
    have hp : (∏ j : Fin 24, minor v (point f j) (d j).1 (d j).2) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
    exact hp (h d)

theorem oneSided_iff_finite (f : Form) (A : End) :
    OneSided (Roots f) A ↔ ∀ k : Fin 24, VectorSafe f (A *ᵥ point f k) := by
  constructor
  · intro h k
    exact h _ (point_mem f k)
  · intro h v hv
    obtain ⟨k,c,hc,rfl⟩ := (roots_iff f v).mp hv
    exact (representative_independent (roots_saturated f) A (point f k) hc).mpr (h k)

abbrev Entry := Fin 4 × Fin 4
abbrev Polynomial := MvPolynomial Entry ℂ
def sideMatrix (b : Bool) (A : End) : End := if b then sharp A else A

/-- The adjoint variables are the literal J A^T J entries. -/
def entryPolynomial (b : Bool) (i j : Fin 4) : Polynomial :=
  if b then MvPolynomial.C (frobeniusSigns i)*MvPolynomial.X (j,i)*
    MvPolynomial.C (frobeniusSigns j) else MvPolynomial.X (i,j)
def imagePolynomial (f : Form) (b : Bool) (k : Fin 24) (i : Fin 4) : Polynomial :=
  ∑ j : Fin 4, entryPolynomial b i j*MvPolynomial.C (point f k j)
def minorPolynomial (f : Form) (b : Bool) (k j : Fin 24) (a c : Fin 4) : Polynomial :=
  imagePolynomial f b k a*MvPolynomial.C (point f j c)-
    imagePolynomial f b k c*MvPolynomial.C (point f j a)
def systemPolynomial (f : Form) (b : Bool) (k : Fin 24) (d : MinorChoice) : Polynomial :=
  ∏ j : Fin 24, minorPolynomial f b k j (d j).1 (d j).2

def Equations (f : Form) (A : End) : Prop :=
  ∀ b : Bool, ∀ k : Fin 24, ∀ d : MinorChoice,
    MvPolynomial.eval (fun ij : Entry => A ij.1 ij.2) (systemPolynomial f b k d) = 0

theorem eval_imagePolynomial (f : Form) (b : Bool) (k : Fin 24) (i : Fin 4) (A : End) :
    MvPolynomial.eval (fun ij : Entry => A ij.1 ij.2) (imagePolynomial f b k i) =
      (sideMatrix b A *ᵥ point f k) i := by
  cases b <;>
    simp [imagePolynomial,entryPolynomial,sideMatrix,Matrix.mulVec,dotProduct,sharp_apply]

theorem eval_systemPolynomial (f : Form) (b : Bool) (k : Fin 24) (d : MinorChoice) (A : End) :
    MvPolynomial.eval (fun ij : Entry => A ij.1 ij.2) (systemPolynomial f b k d) =
      ∏ j : Fin 24, minor (sideMatrix b A *ᵥ point f k) (point f j) (d j).1 (d j).2 := by
  simp only [systemPolynomial,map_prod,minorPolynomial,map_sub,map_mul,
    MvPolynomial.eval_C,eval_imagePolynomial,minor]

/-- Exact necessary and sufficient polynomial equations, on arbitrary
complex endomorphisms. In particular zero outputs and both sides survive. -/
theorem twoSided_iff_equations (f : Form) (A : End) :
    TwoSided (Roots f) A ↔ Equations f A := by
  constructor
  · intro h b k d
    have hh : VectorSafe f (sideMatrix b A *ᵥ point f k) := by
      cases b
      · exact h.1 _ (point_mem f k)
      · exact h.2 _ (point_mem f k)
    rw [eval_systemPolynomial]
    exact (exists_lineCone_iff_products f _).mp ((vectorSafe_iff_lineCone f _).mp hh) d
  · intro h
    have hh (b : Bool) : OneSided (Roots f) (sideMatrix b A) := by
      apply (oneSided_iff_finite f _).mpr
      intro k
      apply (vectorSafe_iff_lineCone f _).mpr
      apply (exists_lineCone_iff_products f _).mpr
      intro d
      exact (eval_systemPolynomial f b k d A).symm.trans (h b k d)
    exact ⟨hh false,hh true⟩

theorem literalDeck_iff_equations (f : Form) (q : FourTensor) :
    LiteralDeck f q ↔ ∀ e : PortOrder, Equations f (transferMatrix q e) := by
  rw [deck_iff_transfer_all_orders]
  exact forall_congr' (fun e => twoSided_iff_equations f (transferMatrix q e))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
