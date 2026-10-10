import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinPhaseActual
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinRMPhaseTable
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramNorm

/-! The seven actual two-copy signed-RM phase probes. Every boundary order,
internal shift and sign is literal data; the only physical ingredients are
two original input copies, retained I, and actual ordered J representatives. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRMPhaseProgram
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace A
export GlobalCloseCompletionKleinPhaseActual (phase phase_actual translate_upTo join_upTo)
end A
namespace C
export GlobalCloseCompletionKleinCharacterResources (bell)
end C
namespace W
export GlobalCloseCompletionKleinH8Wiring (join value scale)
end W
namespace B
export GlobalCloseCompletionC2BitTranslateActual (translate)
end B
namespace P
export Holant.OpenNetworkComposition.ProjectiveSubstitution (realizesUpTo_reindex)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def firstData : Fin 7→Fin 8→Fin 8 := ![![0,1,2,3,4,5,6,7],![7,1,0,3,2,6,4,5],![5,4,6,1,3,2,7,0],![7,2,3,0,5,6,4,1],![1,5,4,3,7,2,0,6],![2,7,6,5,4,1,3,0],![6,4,2,5,3,7,0,1]]
def firstInverse : Fin 7→Fin 8→Fin 8 := ![![0,1,2,3,4,5,6,7],![2,1,4,3,6,7,5,0],![7,3,5,4,1,0,2,6],![3,7,1,2,6,4,5,0],![6,0,5,3,2,1,7,4],![7,5,0,6,4,3,2,1],![6,7,2,4,1,3,0,5]]
def secondData : Fin 7→Fin 8→Fin 8 := ![![2,5,4,0,3,7,1,6],![2,1,6,0,7,3,4,5],![4,5,3,2,6,1,7,0],![0,4,1,7,6,5,2,3],![1,3,7,4,2,5,0,6],![4,2,3,7,0,1,5,6],![0,4,2,5,1,3,6,7]]
def secondInverse : Fin 7→Fin 8→Fin 8 := ![![3,6,0,4,2,1,7,5],![3,1,0,5,6,7,2,4],![7,5,3,2,0,1,4,6],![0,2,6,7,1,5,4,3],![6,0,4,1,3,5,7,2],![4,5,1,2,0,6,7,3],![0,4,2,5,1,3,6,7]]

def first (j : Fin 7) : Equiv.Perm (Fin 8) where
  toFun := firstData j
  invFun := firstInverse j
  left_inv  := by
    have h : ∀j i,firstInverse j (firstData j i)=i := by decide
    exact h j
  right_inv  := by
    have h : ∀j i,firstData j (firstInverse j i)=i := by decide
    exact h j
def second (j : Fin 7) : Equiv.Perm (Fin 8) where
  toFun := secondData j
  invFun := secondInverse j
  left_inv  := by
    have h : ∀j i,secondInverse j (secondData j i)=i := by decide
    exact h j
  right_inv  := by
    have h : ∀j i,secondData j (secondInverse j i)=i := by decide
    exact h j
def base : Equiv.Perm (Fin 8) where
  toFun := ![2,5,4,0,3,7,1,6]
  invFun := ![3,6,0,4,2,1,7,5]
  left_inv := by decide
  right_inv := by decide

def phaseMask : Fin 7→ℕ := ![0,52,28,31,8,30,10]
def shiftMask : Fin 7→ℕ := ![0,50,30,13,62,14,2]

def phaseSet (j : Fin 7) : Finset (Fin 8) :=
  Finset.univ.filter (fun i : Fin 8=>(2 : ℕ) ≤ i.val ∧ (phaseMask j).testBit (7-i.val)=true)
def shiftWord (j : Fin 7) (i : Fin 8) : Bool :=
  if i.val<2 then false else (shiftMask j).testBit (7-i.val)

variable {K : Type*} [Field K]

def program (f : Signature K 8) (j : Fin 7) : Signature K 4 :=
  W.join (A.phase (phaseSet j) (Tensor.reindex (first j).symm f))
    (Tensor.reindex base (B.translate (Tensor.reindex (second j).symm f) (shiftWord j)))

theorem actual (F : SignatureFamily K) (identity : RetainsIdentity F)
    (J : Gadget.RealizesUpTo F .disequality (C.bell 1 1))
    (f : Signature K 8) (source : Gadget.RealizesUpTo F .disequality f) (j : Fin 7) :
    Gadget.RealizesUpTo F .disequality (program f j) := by
  have left := A.phase_actual F J _ (P.realizesUpTo_reindex F (first j).symm f source) (phaseSet j)
  have right := A.translate_upTo F identity _ (P.realizesUpTo_reindex F (second j).symm f source) (shiftWord j)
  exact A.join_upTo F identity _ _ left (P.realizesUpTo_reindex F base _ right)

theorem reindex_scale {m n : ℕ} (p : Fin m≃Fin n) (f : Signature K m) (c : K) :
    Tensor.reindex p (c • f)=c • Tensor.reindex p f := rfl

theorem phase_scale {n : ℕ} (s : Finset (Fin n)) (f : Signature K n) (c : K) :
    A.phase s (c • f)=c • A.phase s f := by
  funext x
  simp only [A.phase,Pi.smul_apply,smul_eq_mul]
  ring

theorem translate_scale {n : ℕ} (f : Signature K n) (mask : Fin n→Bool) (c : K) :
    B.translate (c • f) mask=c • B.translate f mask := rfl

theorem program_scale (f : Signature K 8) (j : Fin 7) (c : K) :
    program (c • f) j=c^2 • program f j := by
  rw [program,reindex_scale,phase_scale,reindex_scale,translate_scale,reindex_scale,W.scale]
  simp only [pow_two,program]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRMPhaseProgram
end
