import Holant.Certificates.MatchingProductBridge.SymmetricDirections

namespace Holant.Certificates.MatchingProductBridge
noncomputable section

def quaternionCoefficient (U : Binary) : Fin 4 → ℂ :=
  ![(U false false+U true true)/2,
    -(Complex.I/2)*(U false true+U true false),
    (U false true-U true false)/2,
    -(Complex.I/2)*(U false false-U true true)]

theorem quaternionCoefficient_quaternion (v : Fin 4 → ℝ) (i : Fin 4) :
    quaternionCoefficient (quaternion v) i = (v i : ℂ) := by
  fin_cases i <;>
    simp [quaternionCoefficient,quaternion,Q0,Q1,Q2,Q3,Holant.Signature.equality] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem quaternion_injective : Function.Injective quaternion := by
  intro u v h
  funext i
  apply Complex.ofReal_injective
  rw [← quaternionCoefficient_quaternion u i,← quaternionCoefficient_quaternion v i,h]

theorem signBit_ne_zero (b : Bool) : signBit b ≠ 0 := by cases b <;> norm_num [signBit]
theorem signBit_xor (a b : Bool) : signBit (a ^^ b) = signBit a * signBit b := by
  cases a <;> cases b <;> norm_num [signBit]
theorem signBit_twist (a b : Bool) : signBit a * signBit (b ^^ a) = signBit b := by
  cases a <;> cases b <;> norm_num [signBit]

def signVector (ε : Fin 4 → Bool) : Fin 4 → ℝ := fun i => signBit (ε i)

theorem signVector_tetrahedral_direction (g : PlatonicModel) (ε : Fin 4 → Bool) :
    groupDirection g (quaternion (signVector ε)) := by
  let η : Fin 3 → Bool := fun j => ε j.succ ^^ ε 0
  let v : Fin 4 → ℝ := ![1,signBit (η 0),signBit (η 1),signBit (η 2)]
  have hv : modelBase g (quaternion v) := by
    cases g
    · exact Or.inr ⟨η,rfl⟩
    · exact Or.inl (Or.inr ⟨η,rfl⟩)
    · exact Or.inl (Or.inr ⟨η,rfl⟩)
  have he : signVector ε = signBit (ε 0) • v := by
    funext i
    fin_cases i
    · simp [signVector,v]
    · exact (signBit_twist (ε 0) (ε 1)).symm
    · exact (signBit_twist (ε 0) (ε 2)).symm
    · exact (signBit_twist (ε 0) (ε 3)).symm
  rw [he,quaternion_real_smul]
  exact ⟨(signBit (ε 0) : ℂ),Complex.ofReal_ne_zero.mpr (signBit_ne_zero _),_,hv,rfl⟩

def twistVector (π : Equiv.Perm (Fin 4)) (δ : Fin 4 → Bool) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => signBit (δ i) * v (π.symm i)

theorem twistVector_axis (π : Equiv.Perm (Fin 4)) (δ : Fin 4 → Bool) (j : Fin 4) :
    twistVector π δ (axisVector j) = signBit (δ (π j)) • axisVector (π j) := by
  funext i
  by_cases hi : i = π j
  · subst i
    simp [twistVector,axisVector]
  · have hpre : π.symm i ≠ j := by intro h; apply hi; simpa using congrArg π h
    simp [twistVector,axisVector,hi,hpre]

theorem twistVector_sign (π : Equiv.Perm (Fin 4)) (δ ε : Fin 4 → Bool) :
    twistVector π δ (signVector ε) = signVector (fun i => δ i ^^ ε (π.symm i)) := by
  funext i
  exact (signBit_xor _ _).symm

theorem twistVector_add (π : Equiv.Perm (Fin 4)) (δ : Fin 4 → Bool) (u v : Fin 4 → ℝ) :
    twistVector π δ (u+v) = twistVector π δ u+twistVector π δ v := by
  funext i
  simp [twistVector,mul_add]

theorem twistVector_smul (π : Equiv.Perm (Fin 4)) (δ : Fin 4 → Bool) (r : ℝ) (v : Fin 4 → ℝ) :
    twistVector π δ (r • v) = r • twistVector π δ v := by
  funext i
  simp [twistVector,smul_eq_mul]
  ring

end
end Holant.Certificates.MatchingProductBridge
