import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryReciprocal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenDiagonal
import Mathlib.Analysis.Complex.Basic

/-! In an obstructed ordinary source without original hardness, every
actual full even unary has a finite coefficient ratio. Full binary rows
therefore admit one common positive coefficient power. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryFiniteValues
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace D
export NoXGeneralEvenDiagonal (output diagonal)
end D
namespace U
export NoXGeneralUnsignedBinary (restrict restrict_value)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (badRow : B.Block (s:=src.size) (b:=src.b) 2)
variable (badFull : ∀x,badRow.signature src.H x≠0)
variable (badA : ¬Affine (fun x=>(badRow.signature src.H x : AlgebraicComplex)))
variable (badP : ¬Product (fun x=>(badRow.signature src.H x : AlgebraicComplex)))
variable (negative : ¬Tract (GenericOrdinarySource.family G src))
variable (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G)

include badFull badA badP negative noHard in
theorem unary (row : B.Block (s:=src.size) (b:=src.b) 1)
    (h0 : row.signature src.H (fun _=>false)≠0) (h1 : row.signature src.H (fun _=>true)≠0) :
    ∃k : ℕ,0<k ∧ row.signature src.H (fun _=>true)^k=row.signature src.H (fun _=>false)^k := by
  classical
  by_contra none
  apply noHard
  apply NoIOrdinaryReciprocal.countingHard G src badRow badFull badA badP
    (D.output src.H src.e (src.p false) (src.p true) src.he (src.hp false) (src.hp true) row)
    _ _ (D.diagonal src.H src.e (src.p false) (src.p true) src.he (src.hp false) (src.hp true) row) h0 h1
  intro k hk period
  apply none
  refine ⟨k,hk,?_⟩
  rw [div_pow,div_eq_one_iff_eq (pow_ne_zero _ h0)] at period
  exact period

theorem powers_multiple {K : Type} [Monoid K] (x y : K) (k n : ℕ)
    (eqn : x^k=y^k) (divides : k∣n) : x^n=y^n := by
  obtain ⟨t,rfl⟩:=divides
  rw [pow_mul,pow_mul,eqn]

include badFull badA badP negative noHard in
theorem binary (row : B.Block (s:=src.size) (b:=src.b) 2) (full : ∀x,row.signature src.H x≠0) :
    ∃n : ℕ,2≤n ∧ ∀x,row.signature src.H x^n=row.signature src.H ![false,false]^n := by
  let r0:=U.restrict row (![.inl false,.inr 0] : Fin 2→Bool⊕Fin 1)
  let c0:=U.restrict row (![.inr 0,.inl false] : Fin 2→Bool⊕Fin 1)
  let r1:=U.restrict row (![.inl true,.inr 0] : Fin 2→Bool⊕Fin 1)
  have rv0 (x : Fin 1→Bool) : r0.signature src.H x=row.signature src.H ![false,x 0] := by
    rw [U.restrict_value]
    apply congrArg (row.signature src.H)
    funext i;fin_cases i <;> rfl
  have cv0 (x : Fin 1→Bool) : c0.signature src.H x=row.signature src.H ![x 0,false] := by
    rw [U.restrict_value]
    apply congrArg (row.signature src.H)
    funext i;fin_cases i <;> rfl
  have rv1 (x : Fin 1→Bool) : r1.signature src.H x=row.signature src.H ![true,x 0] := by
    rw [U.restrict_value]
    apply congrArg (row.signature src.H)
    funext i;fin_cases i <;> rfl
  obtain ⟨k,hk,kvalue⟩:=unary G src badRow badFull badA badP negative noHard r0 (by rw [rv0];exact full _) (by rw [rv0];exact full _)
  obtain ⟨l,hl,lvalue⟩:=unary G src badRow badFull badA badP negative noHard c0 (by rw [cv0];exact full _) (by rw [cv0];exact full _)
  obtain ⟨t,ht,tvalue⟩:=unary G src badRow badFull badA badP negative noHard r1 (by rw [rv1];exact full _) (by rw [rv1];exact full _)
  simp only [rv0] at kvalue
  simp only [cv0] at lvalue
  simp only [rv1] at tvalue
  let n:=k*l*t*2
  have dn : 2≤n := by
    have positive:=Nat.mul_pos (Nat.mul_pos hk hl) ht
    omega
  have kp : k∣n:=⟨l*t*2,by dsimp [n];ring⟩
  have lp : l∣n:=⟨k*t*2,by dsimp [n];ring⟩
  have tp : t∣n:=⟨k*l*2,by dsimp [n];ring⟩
  have kb:=powers_multiple _ _ k n kvalue kp
  have lc:=powers_multiple _ _ l n lvalue lp
  have td:=powers_multiple _ _ t n tvalue tp
  refine ⟨n,dn,?_⟩
  intro x
  have word : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [word]
  cases x 0 <;> cases x 1
  · rfl
  · exact kb
  · exact lc
  · exact td.trans lc

theorem complex_norm_of_power {x y : ℂ} {n : ℕ} (hn : n≠0) (power : x^n=y^n) :
    Complex.normSq x=Complex.normSq y := by
  have norms : ‖x‖=‖y‖:=
    (pow_left_inj₀ (norm_nonneg x) (norm_nonneg y) hn).mp (by simpa only [norm_pow] using congrArg norm power)
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,norms]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryFiniteValues
end
