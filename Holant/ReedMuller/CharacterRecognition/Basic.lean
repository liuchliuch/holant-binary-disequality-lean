import Holant.ReedMuller.CharacterRecognition.Algebra

/-! Logical-pair coordinates and literal signed-card coefficient hypotheses.
The zero-or-full support hypothesis here still needs the physical support
and quotient-dimension transport before it can be used in source Lemma 7.24. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {r : ℕ}

def mixed (Q : QuadraticPhase r) (j k : Fin r) : ZMod 4 :=
  if j<k then Q.mixed j k else if k<j then Q.mixed k j else 0

def beta (Q : QuadraticPhase r) (j k : Fin r) : ZMod 2 :=
  if mixed Q j k=0 then 0 else 1

@[simp] theorem mixed_self (Q : QuadraticPhase r) (j : Fin r) : mixed Q j j=0 := by
  simp [mixed]
theorem mixed_comm (Q : QuadraticPhase r) (j k : Fin r) : mixed Q j k=mixed Q k j := by
  unfold mixed
  split_ifs
  all_goals try omega
  all_goals ring

theorem mixed_even (Q : QuadraticPhase r) (j k : Fin r) : Even (mixed Q j k) := by
  unfold mixed
  split_ifs with h h
  · exact Q.even_mixed j k h
  · exact Q.even_mixed k j h
  · exact Or.inl rfl

@[simp] theorem evenLift_beta (Q : QuadraticPhase r) (j k : Fin r) :
    TwoTranslate.evenLift (beta Q j k)=mixed Q j k := by
  rcases mixed_even Q j k with h|h <;> simp [beta,h,show (2 : ZMod 4)≠0 from by decide]
@[simp] theorem beta_self (Q : QuadraticPhase r) (j : Fin r) : beta Q j j=0 := by
  simp [beta]
theorem beta_comm (Q : QuadraticPhase r) (j k : Fin r) : beta Q j k=beta Q k j := by
  simp only [beta,mixed_comm Q j k]

/-- Normalize only by the explicitly displayed nonzero constant phase. -/
def phase (Q : QuadraticPhase r) (x : Word r) : ℂ := root (Q.eval x-Q.constant)

theorem source_phase (Q : QuadraticPhase r) (x : Word r) :
    root (Q.eval x)=root Q.constant*phase Q x := by
  rw [phase,←root_add,add_sub_cancel]

theorem phase_ne_zero (Q : QuadraticPhase r) (x : Word r) : phase Q x≠0 := root_ne_zero _

@[simp] theorem eval_origin (Q : QuadraticPhase r) : Q.eval (origin r)=Q.constant := by
  simp [QuadraticPhase.eval,origin]
@[simp] theorem eval_basis (Q : QuadraticPhase r) (j : Fin r) :
    Q.eval (basis j)=Q.constant+Q.linear j := by
  simpa using quadratic_eval_word Q {j}

theorem xor_basis_word (j k : Fin r) (h : j≠k) : xor (basis j) (basis k)=word {j,k} := by
  rw [Finset.pair_comm,word_insert _ _ (by simpa using Ne.symm h),word_singleton]

@[simp] theorem eval_two (Q : QuadraticPhase r) (j k : Fin r) (h : j≠k) :
    Q.eval (xor (basis j) (basis k))=Q.constant+Q.linear j+Q.linear k+mixed Q j k := by
  rw [xor_basis_word j k h,quadratic_eval_word]
  simp [h,Ne.symm h,mixed]
  split_ifs
  all_goals try omega
  all_goals ring

@[simp] theorem phase_origin (Q : QuadraticPhase r) : phase Q (origin r)=1 := by
  simp [phase]
@[simp] theorem phase_basis (Q : QuadraticPhase r) (j : Fin r) :
    phase Q (basis j)=root (Q.linear j) := by simp [phase]

theorem phase_two (Q : QuadraticPhase r) (j k : Fin r) (h : j≠k) :
    phase Q (xor (basis j) (basis k))=
      root (Q.linear j)*root (Q.linear k)*sign (beta Q j k) := by
  rw [phase,eval_two Q j k h]
  have he : Q.constant+Q.linear j+Q.linear k+mixed Q j k-Q.constant=
    Q.linear j+Q.linear k+mixed Q j k := by abel
  rw [he,root_add,root_add,←evenLift_beta,root_evenLift]

theorem eval_three (Q : QuadraticPhase r) (j k m : Fin r)
    (hjk : j≠k) (hjm : j≠m) (hkm : k≠m) :
    Q.eval (xor (xor (basis k) (basis m)) (basis j))=
      Q.constant+Q.linear j+Q.linear k+Q.linear m+
        mixed Q j k+mixed Q j m+mixed Q k m := by
  have hh := quadratic_thirdDifference Q (origin r) (basis k) (basis m) (basis j)
  simp only [thirdDifference,origin_xor,eval_two Q k m hkm,
    eval_two Q k j (Ne.symm hjk),eval_two Q m j (Ne.symm hjm),eval_basis,eval_origin,
    mixed_comm Q k j,mixed_comm Q m j] at hh
  linear_combination hh

theorem phase_three (Q : QuadraticPhase r) (j k m : Fin r)
    (hjk : j≠k) (hjm : j≠m) (hkm : k≠m) :
    phase Q (xor (xor (basis k) (basis m)) (basis j))=
      root (Q.linear j)*root (Q.linear k)*root (Q.linear m)*
        sign (beta Q j k)*sign (beta Q j m)*sign (beta Q k m) := by
  rw [phase,eval_three Q j k m hjk hjm hkm]
  have he : Q.constant+Q.linear j+Q.linear k+Q.linear m+
        mixed Q j k+mixed Q j m+mixed Q k m-Q.constant=
      Q.linear j+Q.linear k+Q.linear m+mixed Q j k+mixed Q j m+mixed Q k m := by abel
  rw [he]
  simp only [root_add,←evenLift_beta,root_evenLift]

def card (Q : QuadraticPhase r) (j : Fin r) (b : ZMod 2) (x : Word r) : ℂ :=
  phase Q x+sign b*phase Q (xor x (basis j))

/-- A full-support sign character, restricted to the literal logical slice. -/
def SliceCharacter (f : Word r → ℂ) (j : Fin r) : Prop :=
  ∃ c : ℂ, c≠0 ∧ ∃ ell : Character r, ∀ x,x j=false → f x=c*sign (ell (vectorWord x))

/-- These are equations about actual coefficient sums, not assumptions about
linear or quadratic phase parameters. Geometric transport supplies fullness. -/
def PairCards (Q : QuadraticPhase r) : Prop := ∀ j b,
  (∀ x,x j=false → card Q j b x=0) ∨ SliceCharacter (card Q j b) j

@[simp] theorem vectorWord_origin : vectorWord (origin r)=0 := by
  funext j; rfl

theorem vectorWord_xor (x y : Word r) : vectorWord (xor x y)=vectorWord x+vectorWord y := by
  funext j
  cases hx : x j <;> cases hy : y j <;> simp [vectorWord,AffinePhase.xor,hx,hy,boolEquiv]
  rfl

theorem SliceCharacter.square {f : Word r → ℂ} {j : Fin r}
    (h : SliceCharacter f j) (x : Word r) (hx : x j=false) : f x^2=f (origin r)^2 := by
  obtain ⟨c,hc,ell,he⟩ := h
  have hs : sign (ell (vectorWord x))^2=1 := by rw [pow_two,sign_square]
  simp only [he x hx,he (origin r) rfl,vectorWord_origin,map_zero,sign_zero,mul_one,mul_pow,hs]

theorem SliceCharacter.rectangle {f : Word r → ℂ} {j : Fin r}
    (h : SliceCharacter f j) (x y : Word r) (hx : x j=false) (hy : y j=false) :
    f (xor x y)*f (origin r)=f x*f y := by
  obtain ⟨c,hc,ell,he⟩ := h
  rw [he (xor x y) (by simp [hx,hy]),he (origin r) rfl,he x hx,he y hy,
    vectorWord_origin,map_zero,sign_zero,mul_one,vectorWord_xor,map_add,sign_add]
  ring

theorem SliceCharacter.nonzero {f : Word r → ℂ} {j : Fin r}
    (h : SliceCharacter f j) (x : Word r) (hx : x j=false) : f x≠0 := by
  obtain ⟨c,hc,ell,he⟩ := h
  rw [he x hx]
  exact mul_ne_zero hc (sign_nonzero _)

end
end Holant.ReedMuller.CharacterRecognition
