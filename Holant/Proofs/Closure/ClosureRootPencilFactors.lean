import Holant.Proofs.Closure.ClosureRootPencilSegre
import Holant.Proofs.Closure.ClosureRootPencilMatrix

/-! Exact ordered factor coordinates of the original four-port tensors.
Analytic endpoint factors are reconstructed from the actual anchor table;
the full outside-support zero equations remain part of the reconstruction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective
open scoped BigOperators

def pairTensor (ports : (Fin 2 × Bool) ≃ Fin 4) (C D : Kernel ℂ) : Signature ℂ 4 :=
  fun x => C (x (ports (0,false))) (x (ports (0,true))) *
    D (x (ports (1,false))) (x (ports (1,true)))

theorem parityCoordinates_supported (p a : Bool) (u v : ℂ) :
    parityCoordinates p u v a (a ^^ p) = if a then v else u := by
  cases p <;> cases a <;> simp [parityCoordinates,parityAxis]

theorem parityCoordinates_off (p a b : Bool) (u v : ℂ) (off : b ≠ (a ^^ p)) :
    parityCoordinates p u v a b=0 := by
  cases p <;> cases a <;> cases b <;> simp_all [parityCoordinates,parityAxis]

theorem rootMonomial_scale {m : ℕ} {B : Kernel ℂ} (h : IsRootMonomial m B)
    (c : ℂ) (hc : c ≠ 0) : IsRootMonomial m (c • B) := by
  rcases h with ⟨h01,h10,h00,h11,hr⟩ | ⟨h00,h11,h01,h10,hr⟩
  · left
    refine ⟨by simp [h01],by simp [h10],mul_ne_zero hc h00,mul_ne_zero hc h11,?_⟩
    simpa only [Pi.smul_apply,smul_eq_mul,mul_div_mul_left _ _ hc] using hr
  · right
    refine ⟨by simp [h00],by simp [h11],mul_ne_zero hc h01,mul_ne_zero hc h10,?_⟩
    simpa only [Pi.smul_apply,smul_eq_mul,mul_div_mul_left _ _ hc] using hr

namespace Product
variable {m : ℕ} {f : Signature ℂ 4} (P : Product m f)

def weight (e : Fin 2) (a : Bool) : ℂ := P.matrix e a (a ^^ P.parity e)

theorem weight_nonzero (e : Fin 2) (a : Bool) : P.weight e a ≠ 0 :=
  (P.parity_spec e a _).mpr rfl

theorem anchor_coordinates (a b : Bool) :
    coordinates P f a b=P.scalar*P.weight 0 a*P.weight 1 b := by
  have he := congrFun P.equation (P.word (bits a b))
  simpa only [coordinates,Fin.prod_univ_two,P.word_first,P.word_second,
    bits_zero,bits_one,weight,mul_assoc] using he

theorem word_reconstruct (x : Word) (hx : f x ≠ 0) :
    P.word (fun e => x (P.ports (e,false)))=x := by
  funext i
  obtain ⟨⟨e,b⟩,rfl⟩ := P.ports.surjective i
  have he := (P.parity_spec e _ _).mp ((P.supported x).mp hx e)
  cases b
  · simp
  · simpa using he.symm

theorem bits_reconstruct (x : Word) (hx : f x ≠ 0) :
    P.word (bits (x (P.ports (0,false))) (x (P.ports (1,false))))=x := by
  have bitsEq : bits (x (P.ports (0,false))) (x (P.ports (1,false))) =
      (fun e => x (P.ports (e,false))) := by
    funext e
    fin_cases e <;> rfl
  rw [bitsEq]
  exact P.word_reconstruct x hx

def leftVariable (Q : Signature ℂ 4) : Kernel ℂ :=
  parityCoordinates (P.parity 1)
    (coordinates P Q false false/P.weight 0 false)
    (coordinates P Q false true/P.weight 0 false)

def rightVariable (Q : Signature ℂ 4) : Kernel ℂ :=
  parityCoordinates (P.parity 0)
    (coordinates P Q false false/P.weight 1 false)
    (coordinates P Q true false/P.weight 1 false)

theorem leftVariable_supported (Q : Signature ℂ 4) (a : Bool) :
    P.leftVariable Q a (a ^^ P.parity 1)=coordinates P Q false a/P.weight 0 false := by
  rw [leftVariable,parityCoordinates_supported]
  cases a <;> rfl

theorem rightVariable_supported (Q : Signature ℂ 4) (a : Bool) :
    P.rightVariable Q a (a ^^ P.parity 0)=coordinates P Q a false/P.weight 1 false := by
  rw [rightVariable,parityCoordinates_supported]
  cases a <;> rfl

theorem left_reconstruct (Q : Signature ℂ 4)
    (outside : ∀ x, f x=0 → Q x=0)
    (fixed : ∀ a b, coordinates P Q a b=
      P.weight 0 a*(coordinates P Q false b/P.weight 0 false)) :
    Q=pairTensor P.ports (P.matrix 0) (P.leftVariable Q) := by
  funext x
  by_cases hx : f x=0
  · have qzero := outside x hx
    have bad : ¬ ∀ e, P.matrix e (x (P.ports (e,false))) (x (P.ports (e,true))) ≠ 0 :=
      fun h => ((P.supported x).mpr h) hx
    push Not at bad
    obtain ⟨e,he⟩ := bad
    fin_cases e
    · change P.matrix 0 (x (P.ports (0,false))) (x (P.ports (0,true)))=0 at he
      change Q x=P.matrix 0 (x (P.ports (0,false))) (x (P.ports (0,true))) *
        P.leftVariable Q (x (P.ports (1,false))) (x (P.ports (1,true)))
      rw [he,zero_mul]
      exact qzero
    · have off : x (P.ports (1,true)) ≠ (x (P.ports (1,false)) ^^ P.parity 1) :=
        fun h => ((P.parity_spec 1 _ _).mpr h) he
      have zero := parityCoordinates_off (P.parity 1) _ _
        (coordinates P Q false false/P.weight 0 false)
        (coordinates P Q false true/P.weight 0 false) off
      simpa only [pairTensor,leftVariable,zero,mul_zero] using qzero
  · rw [←P.bits_reconstruct x hx]
    simp only [pairTensor,P.word_first,P.word_second,bits_zero,bits_one]
    rw [P.leftVariable_supported]
    exact fixed _ _

theorem right_reconstruct (Q : Signature ℂ 4)
    (outside : ∀ x, f x=0 → Q x=0)
    (fixed : ∀ a b, coordinates P Q a b=
      (coordinates P Q a false/P.weight 1 false)*P.weight 1 b) :
    Q=pairTensor P.ports (P.rightVariable Q) (P.matrix 1) := by
  funext x
  by_cases hx : f x=0
  · have qzero := outside x hx
    have bad : ¬ ∀ e, P.matrix e (x (P.ports (e,false))) (x (P.ports (e,true))) ≠ 0 :=
      fun h => ((P.supported x).mpr h) hx
    push Not at bad
    obtain ⟨e,he⟩ := bad
    fin_cases e
    · have off : x (P.ports (0,true)) ≠ (x (P.ports (0,false)) ^^ P.parity 0) :=
        fun h => ((P.parity_spec 0 _ _).mpr h) he
      have zero := parityCoordinates_off (P.parity 0) _ _
        (coordinates P Q false false/P.weight 1 false)
        (coordinates P Q true false/P.weight 1 false) off
      simpa only [pairTensor,rightVariable,zero,zero_mul] using qzero
    · change P.matrix 1 (x (P.ports (1,false))) (x (P.ports (1,true)))=0 at he
      change Q x=P.rightVariable Q (x (P.ports (0,false))) (x (P.ports (0,true))) *
        P.matrix 1 (x (P.ports (1,false))) (x (P.ports (1,true)))
      rw [he,mul_zero]
      exact qzero
  · rw [←P.bits_reconstruct x hx]
    simp only [pairTensor,P.word_first,P.word_second,bits_zero,bits_one]
    rw [P.rightVariable_supported]
    exact fixed _ _

end Product
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
