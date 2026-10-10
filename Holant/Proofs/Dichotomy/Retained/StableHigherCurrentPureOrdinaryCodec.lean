import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentPureOrdinaryData

/-! Reuse the normalized K whole-network program and
the real fixed rational answer-conversion machine. The ordinary source,
the embedded native palette and the existing pin caller need not have
identical fields or identical bases. Their ACTUAL values determine recovery. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPureOrdinarySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines UniversalPairReduction
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.GeneralExtraction

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
abbrev nativeCoefficients := OriginalFamily.coefficient (nativePalette G) KSourceTransport.nativeEdges
abbrev nativePresentation := OriginalFamily.presentation (nativePalette G) KSourceTransport.nativeEdges
abbrev nativeValue := OriginalFamily.value (nativePalette G) KSourceTransport.nativeEdges
abbrev presentation := OriginalFamily.presentation (ordinaryPalette G) KSourceTransport.equalityEdges
abbrev tables := OriginalFamily.tables (ordinaryPalette G) KSourceTransport.equalityEdges
abbrev value := OriginalFamily.value (ordinaryPalette G) KSourceTransport.equalityEdges

/-- The field from actual transformed coefficients contains every displayed
source row and every ordinary edge coefficient. This is not a claim about L. -/
theorem vertex_in_source_field (i : Fin (s+2)) (x : Fin (arity (s:=s) (a:=a) i.val) → Bool) :
    ordinaryPalette G i x∈familyField (OriginalFamily.coefficient
      (ordinaryPalette G) KSourceTransport.equalityEdges) :=
  coefficient_mem_familyField
    (OriginalFamily.coefficient (ordinaryPalette G) KSourceTransport.equalityEdges) (.inl ⟨i,x⟩)
theorem edge_in_source_field (b c : Bool) :
    Signature.equality (K:=AlgebraicComplex) b c∈familyField (OriginalFamily.coefficient
      (ordinaryPalette G) KSourceTransport.equalityEdges) :=
  coefficient_mem_familyField
    (OriginalFamily.coefficient (ordinaryPalette G) KSourceTransport.equalityEdges) (.inr (0,b,c))

/-- The exact same raw graph over the native palette, including every old
nullary, has the pin caller's work-field answer after its coefficient inclusion. -/
theorem native_value_exact (r : Input (s:=s) (a:=a)) :
    (nativeValue G r : AlgebraicComplex)=(Pins.paletteValue G r : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact]
  have hp : Pins.paletteValue G r=
      (r.val.realize r.property (Pins.palette G)
        (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 :=
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.target_evaluate
      (Pins.F G) (Pins.palette G) r
  rw [hp]
  change _=(Pins.K G).subtype _
  rw [←Network.denote_map (Pins.K G).subtype]
  congr 1
  unfold nativePalette RingHomRealization.mapSignature Network.map RawClosedNetwork.realize
  congr 1
  funext e b c
  cases b <;> cases c <;> simp [KSourceTransport.nativeEdges,Signature.disequality]

def nativeAnswer := FamilyAnswerTransport.recover (nativeCoefficients G) (FiniteFamily.coefficient G)
def nativeAnswerComputes : Computes (Pins.F G).encoding (nativePresentation G).encoding (nativeAnswer G) :=
  FamilyAnswerTransport.computes (nativeCoefficients G) (FiniteFamily.coefficient G)
    (OriginalFamily.coefficient_algebraic (nativePalette G) KSourceTransport.nativeEdges)
    (FiniteFamily.coefficient_algebraic G (QuaternaryEqualityTerminal.algebraic G))

theorem native_answer_correct (r : Input (s:=s) (a:=a)) :
    nativeValue G r=nativeAnswer G (Pins.paletteValue G r) :=
  (FamilyAnswerTransport.recover_exact (nativeCoefficients G) (FiniteFamily.coefficient G)
    (nativeValue G r) (Pins.paletteValue G r) (native_value_exact G r).symm).symm

/-- Only a fixed rational matrix is executed on the answer. The equality
above is proved internally; no field-membership test or codec equality is input. -/
def nativeCodec : LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a))
    (nativePresentation G).encoding (Pins.paletteEncoding s a) (Pins.F G).encoding
    (nativeValue G) (Pins.paletteValue G) :=
  controlledOneQueryOfEq (identityComputes (Pins.paletteEncoding s a)) (nativeAnswerComputes G)
    ((QuaternaryUnaryAccess.paletteTables G).outputBound (Pins.F G))
    (nativeValue G) (native_answer_correct G)

theorem inverse_palette : KSourceTransport.nativeSignatures (ordinaryPalette G)=nativePalette G :=
  KSourceTransport.native_ordinary (nativePalette G)

/-- Full normalized K transport: every physical edge has factor ONE, since
the actual certified source K satisfies K^T K=X. No vertex or edge is removed. -/
theorem ordinary_value_exact (r : Input (s:=s) (a:=a)) :
    (nativeValue G r : AlgebraicComplex)=(value G r : AlgebraicComplex) :=
  KSourceTransport.ordinary_value_exact (nativePalette G) r

def ordinaryControlled : LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a))
    (presentation G).encoding (inputEncoding (s:=s) (a:=a)) (nativePresentation G).encoding
    (value G) (nativeValue G) := by
  have R := KSourceTransport.toNative (ordinaryPalette G)
  change LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a)) (presentation G).encoding
    (inputEncoding (s:=s) (a:=a))
    (OriginalFamily.presentation (KSourceTransport.nativeSignatures (ordinaryPalette G))
      KSourceTransport.nativeEdges).encoding
    (value G) (OriginalFamily.value (KSourceTransport.nativeSignatures (ordinaryPalette G))
      KSourceTransport.nativeEdges) at R
  rw [inverse_palette G] at R
  exact R

def outputBound : PolynomialOutputBound (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G) :=
  (tables G).outputBound (presentation G)
theorem native_answer_cost (y : Pins.K G) :
    primitiveCost (nativeAnswerComputes G).machine ((nativeAnswerComputes G).outputs y).steps
      (some (Turing.initList (nativeAnswerComputes G).machine.computer ((Pins.F G).encoding.encode y)))≤
      (primitivePolynomial (nativeAnswerComputes G)).eval ((Pins.F G).encoding.encode y).length :=
  computes_primitive_cost (nativeAnswerComputes G) y

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPureOrdinarySource
