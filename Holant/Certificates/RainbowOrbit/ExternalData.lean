import Holant.Certificates.OctahedralSeparator.GroupRepresentatives

/-! Literal external tetrahedral dictionary, checked over Q(sqrt(2),i).
The sign cases are precisely eq:external-a4-domain in the source. This file
makes no assertion that these are all marked A4 embeddings. -/
namespace Holant.Certificates.RainbowOrbit.External
open Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Inclusion of the twelve tetrahedral representatives into the frozen table. -/
def firstTwelve (k : Fin 12) : Fin 24 := ⟨k.val,by omega⟩

/-- Exact conjugated representatives, with their fixed normalization retained. -/
def raw (k : Fin 12) : Mat := theta 2 (standard (firstTwelve k))

/-- Literal printed representatives, ordered to match the conjugated dictionary. -/
def displayed : Fin 12 → Mat :=
  ![q 0,q 1,q 2-q 3,q 2+q 3,
    q 0+q 1+ms root (q 2),q 0+q 1-ms root (q 3),
    q 0+q 1+ms root (q 3),q 0+q 1-ms root (q 2),
    q 0-q 1+ms root (q 2),q 0-q 1-ms root (q 3),
    q 0-q 1+ms root (q 3),q 0-q 1-ms root (q 2)]

def displayScale : Fin 12 → Scalar := ![1,1,coeff 0 (1/2) 0 0,coeff 0 (1/2) 0 0,1,1,1,1,1,1,1,1]

theorem raw_displayed : ∀ k : Fin 12, raw k = ms (displayScale k) (displayed k) := by
  intro k
  fin_cases k <;> decide +kernel

theorem displayScale_ne_zero : ∀ k : Fin 12, displayScale k ≠ 0 := by decide +kernel

/-- Exactly the four exceptional terms and the eight independent sign terms. -/
def PrintedScalar (U : Mat) : Prop :=
  U = q 0 ∨ U = q 1 ∨
  (∃ b : Bool, U = q 2+ms (scalarSign b) (q 3)) ∨
  ∃ ε δ : Bool, U = q 0+ms (scalarSign ε) (q 1)+ms (scalarSign δ*root) (q 2) ∨
    U = q 0+ms (scalarSign ε) (q 1)+ms (scalarSign δ*root) (q 3)

instance (U : Mat) : Decidable (PrintedScalar U) := by unfold PrintedScalar; infer_instance

theorem displayed_printed : ∀ k : Fin 12, PrintedScalar (displayed k) := by decide +kernel

theorem printed_covers_Q0 : ∃ k : Fin 12, displayed k = q 0 := by decide +kernel

theorem printed_covers_Q1 : ∃ k : Fin 12, displayed k = q 1 := by decide +kernel

theorem printed_covers_pairs : ∀ b : Bool, ∃ k : Fin 12,
    displayed k = q 2+ms (scalarSign b) (q 3) := by decide +kernel

theorem printed_covers_signs2 : ∀ ε δ : Bool, ∃ k : Fin 12,
    displayed k = q 0+ms (scalarSign ε) (q 1)+ms (scalarSign δ*root) (q 2) := by decide +kernel

theorem printed_covers_signs3 : ∀ ε δ : Bool, ∃ k : Fin 12,
    displayed k = q 0+ms (scalarSign ε) (q 1)+ms (scalarSign δ*root) (q 3) := by decide +kernel

theorem printed_iff_displayed (U : Mat) : PrintedScalar U ↔ ∃ k : Fin 12, U = displayed k := by
  constructor
  · rintro (rfl | rfl | ⟨b,rfl⟩ | ⟨ε,δ,h | h⟩)
    · obtain ⟨k,h⟩ := printed_covers_Q0; exact ⟨k,h.symm⟩
    · obtain ⟨k,h⟩ := printed_covers_Q1; exact ⟨k,h.symm⟩
    · obtain ⟨k,h⟩ := printed_covers_pairs b; exact ⟨k,h.symm⟩
    · obtain ⟨k,hk⟩ := printed_covers_signs2 ε δ; exact ⟨k,h.trans hk.symm⟩
    · obtain ⟨k,hk⟩ := printed_covers_signs3 ε δ; exact ⟨k,h.trans hk.symm⟩
  · rintro ⟨k,rfl⟩; exact displayed_printed k

def transposeIndex : Fin 12 → Fin 12 := ![0,1,3,2,7,5,6,4,11,9,10,8]
def transposeScale : Fin 12 → Scalar := ![1,1,-1,-1,1,1,1,1,1,1,1,1]

theorem transposeScale_ne_zero : ∀ k : Fin 12, transposeScale k ≠ 0 := by decide +kernel

theorem raw_transpose : ∀ k : Fin 12,
    mt (raw k) = ms (transposeScale k) (raw (transposeIndex k)) := by
  intro k
  fin_cases k <;> decide +kernel

def inverseIndex : Fin 12 → Fin 12 := ![0,1,2,3,11,10,9,8,7,6,5,4]
def inverseScale : Fin 12 → Scalar := ![1,-1,-1,-1,rat (1/4),rat (1/4),rat (1/4),rat (1/4),rat (1/4),rat (1/4),rat (1/4),rat (1/4)]

theorem inverseScale_ne_zero : ∀ k : Fin 12, inverseScale k ≠ 0 := by decide +kernel

theorem raw_right_inverse : ∀ k : Fin 12,
    mm (raw k) (ms (inverseScale k) (raw (inverseIndex k))) = q 0 := by
  intro k
  fin_cases k <;> decide +kernel

/-- A nonzero 2x2 projective cross minor, against each forbidden axis. -/
theorem omitted_cross : ∀ k : Fin 12, ∀ axis : Fin 2,
    ∃ a b c d : Bool,
      q (if axis=0 then 2 else 3) a b * raw k c d -
        q (if axis=0 then 2 else 3) c d * raw k a b ≠ 0 := by
  intro k axis
  fin_cases k <;> fin_cases axis <;> decide +kernel

end Holant.Certificates.RainbowOrbit.External
