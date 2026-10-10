import Holant.Proofs.Dichotomy.WithoutIdentity.NoIQuaternaryReduction

/-! The no-I endpoint starts from the actual original indexed algebraic
family and its native-X answer field. All original labels are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOriginalInput
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
abbrev coefficients:=OriginalFamily.coefficient G KSourceTransport.nativeEdges
abbrev field:=familyField (coefficients G)
local instance : Algebra ℚ (field G):=(field G).algebra'
abbrev presentation:=OriginalFamily.presentation G KSourceTransport.nativeEdges
abbrev tables:=OriginalFamily.tables G KSourceTransport.nativeEdges
abbrev value:=OriginalFamily.value G KSourceTransport.nativeEdges

def table (i : Fin s) : Signature (field G) (a i.val):=
  fun x=>(presentation G).decode ((tables G).vertex i x)

theorem table_value (i : Fin s) (x : Fin (a i.val)→Bool) :
    (table G i x : AlgebraicComplex)=G i x :=
  familyCoordinates_spec (coefficients G)
    (OriginalFamily.coefficient_algebraic G KSourceTransport.nativeEdges) (.inl ⟨i,x⟩)

theorem literal (i : Fin s) :
    RingHomRealization.mapAny (field G).subtype (⟨a i.val,table G i⟩ : AnySignature (field G))=⟨a i.val,G i⟩ :=
  congrArg (fun f : Signature AlgebraicComplex (a i.val)=>(⟨a i.val,f⟩ : AnySignature AlgebraicComplex))
    (funext (table_value G i))

theorem ambient : GlobalCloseCompletionUnaryDescentSource.ambient (field G) (table G)=
    PaperLiteralEqualityCriterion.family G := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩;exact ⟨i,(literal G i).symm⟩
  · rintro ⟨i,rfl⟩;exact ⟨i,literal G i⟩

theorem tables_exact : NativeAntiTargetSource.base (table G) (presentation G)=tables G := by
  unfold NativeAntiTargetSource.base
  congr 1
  · funext i x
    exact (presentation G).decode.symm_apply_apply _
  · funext i p q
    apply (presentation G).decode.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    have h:=familyCoordinates_spec (coefficients G)
      (OriginalFamily.coefficient_algebraic G KSourceTransport.nativeEdges) (.inr (i,p,q))
    cases p <;> cases q <;> simpa [OriginalFamily.coefficient,KSourceTransport.nativeEdges,Signature.disequality] using h.symm

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 a) (presentation G).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (presentation G).encoding
    ((NativeAntiTargetSource.base (table G) (presentation G)).evaluate (presentation G)) (value G) := by
  rw [tables_exact]
  exact controlledOneQueryOfEq (identityComputes _) (identityComputes _)
    ((tables G).outputBound (presentation G)) (value G) (fun _=>rfl)

theorem lift {n : ℕ} (q : Signature AlgebraicComplex n) (i : Fin s)
    (retained : (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex)=⟨n,q⟩) :
    ∃f : Signature (field G) n,(⟨a i.val,table G i⟩ : AnySignature (field G))=⟨n,f⟩ ∧
      RingHomRealization.mapSignature (field G).subtype f=q := by
  have arity : a i.val=n:=congrArg Sigma.fst retained
  subst n
  refine ⟨table G i,rfl,?_⟩
  have eq:=eq_of_heq (Sigma.mk.inj_iff.mp retained).2
  exact (funext (table_value G i)).trans eq


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOriginalInput
end
