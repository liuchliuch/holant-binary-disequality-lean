import Holant.EightVertex.LocalAffineCollapse.ComplexBasis

/-! The arbitrary-complex common witness has one algebraic eighth-root column
phase. Removing that phase leaves the balanced matrix used in the parity proof. -/
namespace Holant.EightVertex.LocalAffineCollapse
open Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
noncomputable section
set_option backward.isDefEq.respectTransparency false

def complexMatrix (a b c d : ℂ) : Kernel ℂ :=
  fun x y => if x then if y then d else c else if y then b else a
def complexBalanced (a c r : ℂ) : Kernel ℂ := complexMatrix a (a*r) c (-c*r)

theorem complex_pullback_entries (T : Kernel ℂ) :
    Kernel.pullback Signature.disequality T =
      complexMatrix (2*T false false*T true false)
        (T false false*T true true+T false true*T true false)
        (T false false*T true true+T false true*T true false)
        (2*T false true*T true true) := by
  funext x y
  cases x <;> cases y <;>
    simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,Signature.disequality,complexMatrix] <;> ring

theorem complex_pullback_det (T : Kernel ℂ) :
    complexDet (Kernel.pullback Signature.disequality T)= -(complexDet T)^2 := by
  rw [complex_pullback_entries]
  simp only [complexDet,complexMatrix,Bool.false_eq_true,ite_false,ite_true]
  ring

theorem embed_determinant (E : Kernel AlgebraicComplex) :
    (determinant E : ℂ)=complexDet (embedMatrix E) := by
  simp [determinant,complexDet,embedMatrix]

theorem algebraic_edge_nonsingular (T : ComplexBasis) (E : Kernel AlgebraicComplex)
    (hE : embedMatrix E=Kernel.pullback Signature.disequality T.matrix) : determinant E≠0 := by
  intro hz
  have h := congrArg (fun z : AlgebraicComplex => (z:ℂ)) hz
  rw [embed_determinant,hE,complex_pullback_det] at h
  exact (neg_ne_zero.mpr (pow_ne_zero 2 (complexDet_ne_zero T))) h

theorem algebraic_edge_symmetric (T : ComplexBasis) (E : Kernel AlgebraicComplex)
    (hE : embedMatrix E=Kernel.pullback Signature.disequality T.matrix) : Kernel.transpose E=E := by
  funext a b
  apply Subtype.ext
  have hs : Kernel.transpose (embedMatrix E)=embedMatrix E := by
    rw [hE,complex_pullback_entries]
    funext x y
    cases x <;> cases y <;> rfl
  exact congrFun (congrFun hs a) b

theorem complex_localAffine_matrix (T : ComplexBasis) (E : Kernel AlgebraicComplex)
    (hE : embedMatrix E=Kernel.pullback Signature.disequality T.matrix)
    (hL : LocalAffine (kernelSignature E)) :
    ∃ a c : ℂ,a≠0 ∧ c≠0 ∧ ∃rho : AlgebraicComplex,rho^8=1 ∧
      T.matrix=complexBalanced a c rho ∧ (E false false : ℂ)=2*a*c := by
  let Einv := invertibleOfDeterminant E (algebraic_edge_nonsingular T E hE)
  obtain ⟨hdiag,hp,hq,hpow⟩ := localAffine_diagonal_characterization Einv hL
    (algebraic_edge_symmetric T E hE)
  change E=diagonal (E false false) (E true true) at hdiag
  change E false false≠0 at hp
  change E true true≠0 at hq
  change E false false^4=E true true^4 at hpow
  let a := T.matrix false false
  let b := T.matrix false true
  let c := T.matrix true false
  let d := T.matrix true true
  have he0 : (E false false : ℂ)=2*a*c := by
    have h := congrFun (congrFun hE false) false
    simpa [embedMatrix,complex_pullback_entries,complexMatrix,a,c] using h
  have he1 : (E true true : ℂ)=2*b*d := by
    have h := congrFun (congrFun hE true) true
    simpa [embedMatrix,complex_pullback_entries,complexMatrix,b,d] using h
  have hpC : (E false false : ℂ)≠0 := by exact_mod_cast hp
  have hqC : (E true true : ℂ)≠0 := by exact_mod_cast hq
  have hac : 2*a*c≠0 := he0 ▸ hpC
  have hbd : 2*b*d≠0 := he1 ▸ hqC
  have ha : a≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hac).1).2
  have hc : c≠0 := (mul_ne_zero_iff.mp hac).2
  have hb : b≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hbd).1).2
  have hoff : a*d+b*c=0 := by
    have h := congrFun (congrFun hE false) true
    have hz : E false true=0 := by rw [hdiag]; rfl
    simpa [embedMatrix,hz,complex_pullback_entries,complexMatrix,a,b,c,d] using h.symm
  let r := b/a
  have hT : T.matrix=complexBalanced a c r := by
    funext x y
    cases x <;> cases y
    · rfl
    · change b=a*(b/a)
      field_simp [ha]
    · rfl
    · change d= -c*(b/a)
      field_simp [ha]
      linear_combination hoff
  have hpc : (2*a*c)^4=(-(2*a*c)*r^2)^4 := by
    have h : (E false false : ℂ)^4=(E true true : ℂ)^4 := by exact_mod_cast hpow
    rw [he0] at h
    have hlast := congrFun (congrFun hE true) true
    rw [hT,complex_pullback_entries] at hlast
    simp [embedMatrix,complexBalanced,complexMatrix] at hlast
    rw [hlast] at h
    convert h using 1 <;> ring
  have hr8 : r^8=1 := by
    apply mul_left_cancel₀ (pow_ne_zero 4 hac)
    calc
      (2*a*c)^4*r^8 = (-(2*a*c)*r^2)^4 := by ring
      _ = (2*a*c)^4 := hpc.symm
      _ = (2*a*c)^4*1 := by ring
  let rho : AlgebraicComplex := ⟨r,IsIntegral.of_pow (n:=8) (by decide)
    (by rw [hr8]; exact isIntegral_one)⟩
  refine ⟨a,c,ha,hc,rho,?_,hT,he0⟩
  exact Subtype.ext hr8

end
end Holant.EightVertex.LocalAffineCollapse
