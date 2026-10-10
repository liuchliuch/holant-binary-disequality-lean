import Holant.Proofs.Algorithms.TransformRecognition.SparseEvaluation
import Holant.Proofs.AlgebraicRecognition.EncodedSystem


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SparseCoefficientInput
open Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
open Holant.LocalDrafts.EffectiveAlgebraic
variable {n d : ℕ}

def coefficients (D : ArithmeticData d) (S : List (Poly n d)) : List (Coefficient d) :=
  D.unitCode :: -D.unitCode :: S.flatMap (fun p => p.map Prod.snd)

def oneIndex (D : ArithmeticData d) (S : List (Poly n d)) :
    Fin (coefficients D S).length := ⟨0,by simp [coefficients]⟩
def negIndex (D : ArithmeticData d) (S : List (Poly n d)) :
    Fin (coefficients D S).length := ⟨1,by simp [coefficients]⟩

theorem coefficient_mem (D : ArithmeticData d) (S : List (Poly n d))
    (p : Poly n d) (hp : p ∈ S) (t : Term n d) (ht : t ∈ p) :
    t.2 ∈ coefficients D S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨t,ht,rfl⟩⟩))

def index (D : ArithmeticData d) (S : List (Poly n d))
    (p : Poly n d) (hp : p ∈ S) (t : Term n d) (ht : t ∈ p) :
    Fin (coefficients D S).length :=
  ⟨(coefficients D S).idxOf t.2,
    List.idxOf_lt_length_iff.mpr (coefficient_mem D S p hp t ht)⟩

@[simp] theorem get_index (D : ArithmeticData d) (S : List (Poly n d))
    (p : Poly n d) (hp : p ∈ S) (t : Term n d) (ht : t ∈ p) :
    (coefficients D S).get (index D S p hp t ht) = t.2 := by
  exact List.idxOf_get _

def equation (D : ArithmeticData d) (S : List (Poly n d))
    (p : Poly n d) (hp : p ∈ S) :
    EncodedSystem.Equation (coefficients D S).length n :=
  p.attach.map (fun t => (index D S p hp t.1 t.2,t.1.1))

def system (D : ArithmeticData d) (S : List (Poly n d)) :
    EncodedSystem.System (coefficients D S).length n :=
  S.attach.map (fun p => equation D S p.1 p.2)

@[simp] theorem system_length (D : ArithmeticData d) (S : List (Poly n d)) :
    (system D S).length = S.length := by simp [system]
@[simp] theorem equation_length (D : ArithmeticData d) (S : List (Poly n d))
    (p : Poly n d) (hp : p ∈ S) : (equation D S p hp).length = p.length := by
  simp [equation]

variable {K : Type*} [Field K] [Algebra ℚ K] (F : FixedField K d) (φ : K →+* ℂ)
noncomputable section

def values (S : List (Poly n d)) : Fin (coefficients F.toArithmeticData S).length → ℂ :=
  fun i => φ (F.decode ((coefficients F.toArithmeticData S).get i))

@[simp] theorem values_one (S : List (Poly n d)) :
    values F φ S (oneIndex F.toArithmeticData S) = 1 := by
  change φ (F.decode F.unitCode) = 1
  simp
@[simp] theorem values_neg (S : List (Poly n d)) :
    values F φ S (negIndex F.toArithmeticData S) = -1 := by
  change φ (F.decode (-F.unitCode)) = -1
  simp

private theorem encoded_eval {m : ℕ} (w : Fin m → ℂ)
    (e : EncodedSystem.Equation m n) (z : Fin n → ℂ) :
    aeval z (EncodedSystem.polynomial w e) =
      (e.map (fun t => w t.1 * ∏ j, z j ^ t.2 j)).sum := by
  induction e with
  | nil => simp [EncodedSystem.polynomial]
  | cons t e ih =>
    rw [EncodedSystem.polynomial,map_add,ih]
    simp

theorem equation_eval (S : List (Poly n d)) (p : Poly n d) (hp : p ∈ S)
    (z : Fin n → ℂ) :
    aeval z (EncodedSystem.polynomial (values F φ S)
      (equation F.toArithmeticData S p hp)) = SparseEvaluation.evaluate F φ z p := by
  rw [encoded_eval]
  have he : ((equation F.toArithmeticData S p hp).map
      (fun t => values F φ S t.1 * ∏ j, z j ^ t.2 j)) =
      p.map (fun t => φ (F.decode t.2) * ∏ j, z j ^ t.1 j) := by
    simp only [equation,List.map_map,values,Function.comp_def,get_index]
    exact List.attach_map_val (l := p)
      (f := fun t => φ (F.decode t.2) * ∏ j, z j ^ t.1 j)
  rw [he]
  change _ = (eval₂Hom φ z) (denote F p)
  unfold denote
  rw [map_list_sum,List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  change φ (F.decode t.2) * (∏ j, z j ^ t.1 j) =
    eval₂ φ z (monomial (exponent t.1) (F.decode t.2))
  rw [eval₂_monomial]
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  rfl

/-- Every original sparse row appears, with its literal exponents and
coefficient decoded from the computed catalogue; there is no omitted guard,
edge row or cancellation due to deduplicating equations. -/
theorem system_zero_iff (S : List (Poly n d)) (z : Fin n → ℂ) :
    (∀ e ∈ system F.toArithmeticData S,
      aeval z (EncodedSystem.polynomial (values F φ S) e)=0) ↔
    ∀ p ∈ S, SparseEvaluation.evaluate F φ z p=0 := by
  constructor
  · intro h p hp
    rw [← equation_eval F φ S p hp z]
    exact h _ (List.mem_map.mpr ⟨⟨p,hp⟩,List.mem_attach _ _,rfl⟩)
  · intro h e he
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp he
    rw [equation_eval]
    exact h p.1 p.2

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SparseCoefficientInput
