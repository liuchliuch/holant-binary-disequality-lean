import Holant.Projective.BinaryPencil
import Holant.Dihedral.SectorRuling.Source

/-! The exact Z/P/C endpoint classification over the source field. The
complex root-pencil theorem is transported through the actual inclusion;
all phases and coefficients in the conclusion remain algebraic. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Tractable Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.SectorRuling
set_option backward.isDefEq.respectTransparency false

 def axis (p r : Bool) : Mat := fun i j => if i=r ∧ j=(r ^^ p) then 1 else 0
 def matrixPencil (A B : Mat) (t : Scalar) : Mat := fun i j => A i j+t*B i j
 def complexMatrix (A : Mat) : Projective.BinaryMat := fun i j => (A i j : ℂ)

 theorem complexMatrix_injective : Function.Injective complexMatrix := by
  intro A B h
  funext i j
  apply Subtype.ext
  exact congrFun (congrFun h i) j

 theorem complex_scale_axis (a : Scalar) (p r : Bool) :
    complexMatrix (scale a (axis p r))=(a:ℂ) • Projective.parityAxis p r := by
  funext i j
  change ((a*(if i=r ∧ j=(r ^^ p) then 1 else 0):Scalar):ℂ)=
    (a:ℂ)*(if i=r ∧ j=(r ^^ p) then 1 else 0)
  split_ifs <;> simp

 theorem complex_group {m : ℕ} (hm : 0<m) {A : Mat} (hA : A ∈ groupM m) :
    Projective.IsRootMonomial m (complexMatrix A) := by
  obtain ⟨p,t,c,ht,hc,rfl⟩ := group_M_normal_form hm hA
  have ht' : (t:ℂ)^m=1 := by exact_mod_cast ht
  have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne_zero hm
  cases p
  · left
    simp [complexMatrix,scale,M,monomial,hc',hn]
    convert ht' using 1 <;> congr 1 <;> field_simp
  · right
    simp [complexMatrix,scale,M,monomial,hc',hn]
    convert ht' using 1 <;> congr 1 <;> field_simp

/-- No scalar is chosen from the complex field: the multiplier is the ratio
of two original algebraic entries. -/
 theorem scalar_multiple_of_complex {A B : Mat} {s : ℂ}
    (h : complexMatrix B=s • complexMatrix A) : ∃ c : Scalar,B=scale c A := by
  classical
  by_cases hA : A=0
  · refine ⟨0,?_⟩
    apply complexMatrix_injective
    rw [h]
    funext i j
    simp [hA,complexMatrix,scale]
  · have hex : ∃ i j,A i j ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hA (by funext i j; exact hh i j)
    obtain ⟨i,j,hij⟩ := hex
    refine ⟨B i j/A i j,?_⟩
    funext u v
    apply Subtype.ext
    have he := congrFun (congrFun h i) j
    have hf := congrFun (congrFun h u) v
    have hn : (A i j:ℂ) ≠ 0 := by exact_mod_cast hij
    change (B u v:ℂ)=((B i j:ℂ)/(A i j:ℂ))*(A u v:ℂ)
    change (B i j:ℂ)=s*(A i j:ℂ) at he
    change (B u v:ℂ)=s*(A u v:ℂ) at hf
    rw [he,hf]
    field_simp

 theorem scalar_proportional_of_complex {A B : Mat}
    (h : Projective.BinaryProportional (complexMatrix A) (complexMatrix B)) :
    (∃ c : Scalar,B=scale c A) ∨ (∃ c : Scalar,A=scale c B) := by
  rcases (Projective.binaryProportional_iff _ _).mp h with ⟨s,hs⟩|⟨s,hs⟩
  · exact Or.inl (scalar_multiple_of_complex hs)
  · exact Or.inr (scalar_multiple_of_complex hs)

/-- The exact endpoint alternatives used in the six-port proof. P retains a
fixed actual-group matrix; C retains both literal nonzero coefficients and
the finite-root ratio. -/
 def BinaryType (m : ℕ) (A B : Mat) : Prop :=
  (A=0 ∧ B=0) ∨
  (∃ Q : Mat,Q ∈ groupM m ∧ ∃ a b : Scalar,(a ≠ 0 ∨ b ≠ 0) ∧
    A=scale a Q ∧ B=scale b Q) ∨
  (∃ p r : Bool,∃ a b : Scalar,a ≠ 0 ∧ b ≠ 0 ∧ Roots m (b/a) ∧
    A=scale a (axis p r) ∧ B=scale b (axis p (!r)))

 private theorem proportional_type {m : ℕ} (hm : 3≤m) (A B : Mat)
    (hs : ∀ t,Roots m t → matrixPencil A B t=0 ∨ matrixPencil A B t ∈ groupM m)
    (hprop : (∃ c : Scalar,B=scale c A) ∨ (∃ c : Scalar,A=scale c B)) :
    (A=0 ∧ B=0) ∨
      ∃ Q : Mat,Q ∈ groupM m ∧ ∃ a b : Scalar,(a ≠ 0 ∨ b ≠ 0) ∧
        A=scale a Q ∧ B=scale b Q := by
  classical
  have nonzero_sample : A ≠ 0 ∨ B ≠ 0 → ∃ t,Roots m t ∧ matrixPencil A B t ≠ 0 := by
    intro hn
    obtain ⟨t,ht,hne,_⟩ := third_root hm 1 1 (Roots.one m) (Roots.one m)
    by_contra hh
    push_neg at hh
    have h1 := hh 1 (Roots.one m)
    have ht' := hh t ht
    have hB : B=0 := by
      funext i j
      have h0 := congrFun (congrFun h1 i) j
      have h2 := congrFun (congrFun ht' i) j
      change A i j+1*B i j=0 at h0
      change A i j+t*B i j=0 at h2
      have hmul : (t-1)*B i j=0 := by linear_combination h2-h0
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
    have hA : A=0 := by funext i j; simpa [matrixPencil,hB] using congrFun (congrFun h1 i) j
    exact hn.elim (fun h => h hA) (fun h => h hB)
  by_cases hz : A=0 ∧ B=0
  · exact Or.inl hz
  · right
    have hn : A ≠ 0 ∨ B ≠ 0 := by tauto
    obtain ⟨t,ht,hnt⟩ := nonzero_sample hn
    have hQ := (hs t ht).resolve_left hnt
    rcases hprop with ⟨c,hc⟩|⟨c,hc⟩
    · have hd : 1+t*c ≠ 0 := by
        intro hd
        apply hnt
        funext i j
        simp only [matrixPencil,hc,scale,Pi.zero_apply]
        linear_combination hd*A i j
      refine ⟨matrixPencil A B t,hQ,(1+t*c)⁻¹,c/(1+t*c),
        Or.inl (inv_ne_zero hd),?_,?_⟩ <;>
        funext i j <;> simp only [matrixPencil,hc,scale] <;> field_simp [hd, show 1+c*t ≠ 0 by simpa [mul_comm] using hd] <;> ring
    · have hd : c+t ≠ 0 := by
        intro hd
        apply hnt
        funext i j
        simp only [matrixPencil,hc,scale,Pi.zero_apply]
        linear_combination hd*B i j
      refine ⟨matrixPencil A B t,hQ,c/(c+t),(c+t)⁻¹,
        Or.inr (inv_ne_zero hd),?_,?_⟩ <;>
        funext i j <;> simp only [matrixPencil,hc,scale] <;> field_simp [hd] <;> ring

 theorem binary_type {m : ℕ} (hm : 3≤m) (A B : Mat)
    (hs : ∀ t,Roots m t → matrixPencil A B t=0 ∨ matrixPencil A B t ∈ groupM m) :
    BinaryType m A B := by
  have hc : ∀ t : ℂ,t^m=1 →
      Projective.binaryPencil (complexMatrix A) (complexMatrix B) t=0 ∨
      Projective.IsRootMonomial m (Projective.binaryPencil (complexMatrix A) (complexMatrix B) t) := by
    intro t ht
    let z := Projective.CyclicPhasePencil.algebraicRoot (by omega : 0<m) t ht
    have hz : Roots m z := Projective.CyclicPhasePencil.algebraicRoot_pow _ _ _
    have he : complexMatrix (matrixPencil A B z)=Projective.binaryPencil (complexMatrix A) (complexMatrix B) t := by
      funext i j
      rfl
    rcases hs z hz with hh|hh
    · left
      rw [←he,hh]
      rfl
    · right
      rw [←he]
      exact complex_group (by omega) hh
  rcases Projective.binary_pencil_classification_endpoints hm (complexMatrix A) (complexMatrix B) hc with hp|hC
  · rcases proportional_type hm A B hs (scalar_proportional_of_complex hp) with hz|hp
    · exact Or.inl hz
    · exact Or.inr (Or.inl hp)
  · right; right
    obtain ⟨p,l,t,hl,ht,h|h⟩ := hC
    · let a := A false p
      let b := B true (!p)
      have ha : (a:ℂ)=l := by
        have hh := congrFun (congrFun h.1 false) p
        simpa [a,complexMatrix,Projective.parityAxis] using hh
      have hb : (b:ℂ)=l*t := by
        have hh := congrFun (congrFun h.2 true) (!p)
        simpa [b,complexMatrix,Projective.parityAxis] using hh
      have ht0 : t ≠ 0 := by intro hz; simp [hz,show m≠0 by omega] at ht
      refine ⟨p,false,a,b,?_,?_,?_,?_,?_⟩
      · intro hz; have := congrArg (fun z : Scalar => (z:ℂ)) hz; exact hl (by simpa [ha] using this)
      · intro hz; have := congrArg (fun z : Scalar => (z:ℂ)) hz; exact mul_ne_zero hl ht0 (by simpa [hb] using this)
      · change (b/a)^m=1
        apply Subtype.ext
        change ((b:ℂ)/(a:ℂ))^m=1
        rw [ha,hb,mul_div_cancel_left₀ _ hl]
        exact ht
      · apply complexMatrix_injective
        rw [complex_scale_axis,ha]
        exact h.1
      · apply complexMatrix_injective
        rw [complex_scale_axis,hb]
        exact h.2
    · let a := A true (!p)
      let b := B false p
      have ha : (a:ℂ)=l*t := by
        have hh := congrFun (congrFun h.1 true) (!p)
        simpa [a,complexMatrix,Projective.parityAxis] using hh
      have hb : (b:ℂ)=l := by
        have hh := congrFun (congrFun h.2 false) p
        simpa [b,complexMatrix,Projective.parityAxis] using hh
      have ht0 : t ≠ 0 := by intro hz; simp [hz,show m≠0 by omega] at ht
      refine ⟨p,true,a,b,?_,?_,?_,?_,?_⟩
      · intro hz; have := congrArg (fun z : Scalar => (z:ℂ)) hz; exact mul_ne_zero hl ht0 (by simpa only [ha,AlgebraicComplex.coe_zero] using this)
      · intro hz; have := congrArg (fun z : Scalar => (z:ℂ)) hz; exact hl (by simpa [hb] using this)
      · change (b/a)^m=1
        apply Subtype.ext
        change ((b:ℂ)/(a:ℂ))^m=1
        rw [ha,hb]
        have he : l/(l*t)=t⁻¹ := by field_simp
        rw [he,inv_pow,ht,inv_one]
      · apply complexMatrix_injective
        rw [complex_scale_axis,ha]
        exact h.1
      · apply complexMatrix_injective
        rw [complex_scale_axis,hb]
        exact h.2

end Holant.Dihedral.SixPortBase
