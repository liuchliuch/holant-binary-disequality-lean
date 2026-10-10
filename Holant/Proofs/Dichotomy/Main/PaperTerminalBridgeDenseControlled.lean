import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Controlled exhaustive dense endpoint. The infinite-ratio branch retains
the complete query and answer bounds until it reaches the exact original
no-I table. It can therefore be composed through later coefficient-field
and factor-table sources without an uncontrolled reduction assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseControlled
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace S
export NativeAntiTargetSource (base)
export PaperTerminalBridgeDenseSemantic (family)
end S
namespace A
export PaperTerminalBridgeAntiGroup (Available)
end A
namespace R
export PaperTerminalBridgeDenseSource (OneSided ComplementOutput oneSided_of_not_safe)
end R
namespace D
export PaperTerminalBridgeFiniteDeck (NoOneSided classification)
end D
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapFamily)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

def target : NoIOrdinaryRaw.Target where
  Input:=ExactSignatureTables.Input s 1 a
  Output:=K
  inputEncoding:=RawClosedNetwork.validatedEncoding s 1 a
  outputEncoding:=F.encoding
  value:=(S.base H F).evaluate F

theorem infinite_hard (q : Signature K 4) (label : Fin s)
    (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,q⟩)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
    (different : ¬PaperTerminalBridgeDenseOrders.EqualProducts q)
    (t : K) (nonzero : t≠0) (actual : A.Available (S.family H) t)
    (infinite : ¬IsOfFinOrder t) : (target H F).Hard := by
  intro α ea count w
  have notone : t≠1 := by
    rintro rfl
    exact infinite (isOfFinOrder_iff_pow_eq_one.mpr ⟨1,by omega,by simp⟩)
  obtain ⟨c,hc,N,form⟩ := PaperTerminalBridgeDenseSemantic.output H t actual notone
  have unbounded : ∀n : ℕ,0<n→((c*t)/c)^n≠1 := by
    intro n hn root
    apply infinite
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n,hn,?_⟩
    have ratio : c*t/c=t := by field_simp
    rwa [ratio] at root
  exact ⟨PaperTerminalBridgeDenseInfinite.source H F q label literal even dense different
    N c (c*t) hc (mul_ne_zero hc nonzero) unbounded form w⟩

def Outcome (phi : K→+*AlgebraicComplex) : Prop :=
  (target H F).Hard ∨ R.OneSided (S.family H) ∨
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor (RH.mapFamily phi (S.family H)) ∨
      R.ComplementOutput (S.family H)

theorem source (phi : K→+*AlgebraicComplex) (q : Signature K 4) (label : Fin s)
    (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,q⟩)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q) : Outcome H F phi := by
  classical
  have actual : Gadget.Realizes (S.family H) .disequality q :=
    Gadget.realizes_of_mem _ _ _ ⟨label,literal⟩
  by_cases products : PaperTerminalBridgeDenseOrders.EqualProducts q
  · exact Or.inr (Or.inr (Or.inl
      (PaperTerminalBridgeEqualProductsAnchor.source phi (S.family H) q actual even dense products)))
  by_cases safe : D.NoOneSided (S.family H)
  · by_cases torsion : ∀t : K,A.Available (S.family H) t→t≠0→IsOfFinOrder t
    · rcases D.classification (S.family H) (PaperTerminalBridgeCancellationField.embedding (K:=K)).toRingHom
          q actual even dense safe torsion with middle | complementary
      · exact Or.inr (Or.inr (Or.inr
          (PaperTerminalBridgeEqualProductsMiddleComplement.source phi (S.family H) q actual even dense middle)))
      · obtain ⟨ε,square,b,c,d⟩ := complementary
        exact Or.inr (Or.inr (Or.inr
          (PaperTerminalBridgeComplementSign.source (S.family H) q actual even dense ε square b c d)))
    · push Not at torsion
      obtain ⟨t,act,nonzero,infinite⟩ := torsion
      exact Or.inl (infinite_hard H F q label literal even dense products t nonzero act infinite)
  · exact Or.inr (Or.inl (R.oneSided_of_not_safe (S.family H) safe))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseControlled
end
