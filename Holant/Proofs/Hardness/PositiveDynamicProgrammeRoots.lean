import Holant.Proofs.Hardness.PositiveDynamicProgrammeEmitter
import Holant.Proofs.Hardness.ThreeModeProgrammeRoots

/-! Genuine size-dependent stage/root preprocessing. Only a,b,c and the fixed
positive damping multiplier are construction data; m and every n=C*(m+1),
formula, power, root and list frame are computed from input bytes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicProgrammeRoots
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing BinaryInterpolation
namespace E
export PositiveDynamicProgrammeEmitter (unary Emits constant add mul power evaluate)
end E
namespace P
export PositiveDynamicProgrammeFormulas (Formula coefficients lam mu nu root desired eval_root eval_desired eval_lam eval_mu eval_nu)
end P
namespace R
export ThreeModeProgrammeRoots (rootEncoding rootM rootI rootJ rootExponent indicesComputes)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev unary := E.unary
variable (C : ℕ)

def stageLength (m : ℕ) : ℕ := C*(m+1)
def lengthComputes : Computes unary unary (stageLength C) :=
  (pairComputes (constantComputes unary unary C) WeightCompiler.successorComputes).andThen
    WeightCompiler.multiplyUnaryComputes

def lamEmits {X : Type} (e : Encoding X Bool) (n : X→ℕ) (wn : Computes e unary n) :
    E.Emits e (fun x=>P.lam (n x)) :=
  E.mul (E.add (E.power n wn (E.constant e (.literal 0)))
    (E.mul (E.constant e (.literal 3)) (E.power n wn (E.constant e (.literal 1)))))
    (E.constant e (.literal 4))
def BEmits {X : Type} (e : Encoding X Bool) (n : X→ℕ) (wn : Computes e unary n) :
    E.Emits e (fun x=>PositiveDynamicProgrammeFormulas.B (n x)) :=
  E.mul (E.add (E.power n wn (E.constant e (.literal 0)))
    (E.power n wn (E.constant e (.literal 1)))) (E.constant e (.literal 4))
def muEmits {X : Type} (e : Encoding X Bool) (n : X→ℕ) (wn : Computes e unary n) :
    E.Emits e (fun x=>P.mu (n x)) :=
  E.add (BEmits e n wn) (E.power n wn (E.constant e (.literal 2)))
def nuEmits {X : Type} (e : Encoding X Bool) (n : X→ℕ) (wn : Computes e unary n) :
    E.Emits e (fun x=>P.nu (n x)) :=
  E.add (BEmits e n wn) (E.mul (E.constant e (.literal 3))
    (E.power n wn (E.constant e (.literal 2))))

def rootEmits : E.Emits R.rootEncoding (fun x=>P.root (stageLength C x.1) x.1 x.2) :=
  E.mul (E.mul
    (E.power (fun x : ℕ×(ℕ×ℕ)=>x.1-x.2.1-x.2.2) R.rootExponent
      (lamEmits R.rootEncoding _ (R.rootM.andThen (lengthComputes C))))
    (E.power (fun x : ℕ×(ℕ×ℕ)=>x.2.1) R.rootI
      (muEmits R.rootEncoding _ (R.rootM.andThen (lengthComputes C)))))
    (E.power (fun x : ℕ×(ℕ×ℕ)=>x.2.2) R.rootJ
      (nuEmits R.rootEncoding _ (R.rootM.andThen (lengthComputes C))))

def desiredEmits : E.Emits unary (fun m=>P.desired (stageLength C m) m) :=
  E.power id (identityComputes unary) (lamEmits unary _ (lengthComputes C))

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} (F : FixedField K d) (a b c : K)

def lam (m : ℕ) : K := PositiveDynamicSeparation.lam a b (stageLength C m)
def mu (m : ℕ) : K := PositiveDynamicSeparation.mu a b c (stageLength C m)
def nu (m : ℕ) : K := PositiveDynamicSeparation.nu a b c (stageLength C m)
def root (x : ℕ×(ℕ×ℕ)) : K := ThreeModeAnnihilator.mode x.1
  (lam C a b x.1) (mu C a b c x.1) (nu C a b c x.1) x.2

def rootComputes : Computes R.rootEncoding F.encoding (root C a b c) :=
  congrComputes (E.evaluate F a b c (rootEmits C)) (fun x=>P.eval_root a b c _ _ _)

def desiredComputes : Computes unary F.encoding (fun m=>(lam C a b m)^m) :=
  congrComputes (E.evaluate F a b c (desiredEmits C)) (fun m=>P.eval_desired a b c _ _)

def lamComputes : Computes unary F.encoding (lam C a b) :=
  congrComputes (E.evaluate F a b c (lamEmits unary _ (lengthComputes C)))
    (fun m=>P.eval_lam a b c _)
def muComputes : Computes unary F.encoding (mu C a b c) :=
  congrComputes (E.evaluate F a b c (muEmits unary _ (lengthComputes C)))
    (fun m=>P.eval_mu a b c _)
def nuComputes : Computes unary F.encoding (nu C a b c) :=
  congrComputes (E.evaluate F a b c (nuEmits unary _ (lengthComputes C)))
    (fun m=>P.eval_nu a b c _)

def roots (m : ℕ) : List K := (ThreeModeAnnihilator.rootIndices m).map
  (ThreeModeAnnihilator.mode m (lam C a b m) (mu C a b c m) (nu C a b c m))
def rootsComputes : Computes unary (framedListEncoding F.encoding) (roots C a b c) :=
  (pairComputes (identityComputes unary) R.indicesComputes).andThen
    (UniversalPairReduction.SmoothingCompiler.mapListComputes unary
      ThreeModeProgrammeRoots.pairUnary F.encoding
      (fun m ij=>root C a b c (m,ij)) (rootComputes C F a b c))

def preprocessing (m : ℕ) : List K×K := (roots C a b c m,(lam C a b m)^m)
def preprocessingComputes : Computes unary
    (pairEncoding (framedListEncoding F.encoding) F.encoding) (preprocessing C a b c) :=
  pairComputes (rootsComputes C F a b c) (desiredComputes C F a b c)

@[simp] theorem preprocessing_zero : preprocessing C a b c 0=([],1) := by
  simp [preprocessing,roots,ThreeModeAnnihilator.rootIndices]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicProgrammeRoots
