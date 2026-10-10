import Holant.Pauli.ExoticKlein.SixPortIntegerCertificate

/-! The literal C2 six-port integer problem. Its unknowns are all 64 original
complex coefficients. Every card is an exact I/X pair contraction; the finite
matching lines include the zero scalar. This file defines the checked
certificate interface and does not assert finite coverage by itself. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SixPortProblem
open Holant
open Holant.Pauli.ExoticKlein.SixPort
open IntegerCertificate LinearCertificate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def inputTable : Fin 30→Fin 32→Fin 64 :=
  ![![0,3,4,7,8,11,12,15,16,19,20,23,24,27,28,31,32,35,36,39,40,43,44,47,48,51,52,55,56,59,60,63],
    ![2,1,6,5,10,9,14,13,18,17,22,21,26,25,30,29,34,33,38,37,42,41,46,45,50,49,54,53,58,57,62,61],
    ![0,5,2,7,8,13,10,15,16,21,18,23,24,29,26,31,32,37,34,39,40,45,42,47,48,53,50,55,56,61,58,63],
    ![4,1,6,3,12,9,14,11,20,17,22,19,28,25,30,27,36,33,38,35,44,41,46,43,52,49,54,51,60,57,62,59],
    ![0,9,2,11,4,13,6,15,16,25,18,27,20,29,22,31,32,41,34,43,36,45,38,47,48,57,50,59,52,61,54,63],
    ![8,1,10,3,12,5,14,7,24,17,26,19,28,21,30,23,40,33,42,35,44,37,46,39,56,49,58,51,60,53,62,55],
    ![0,17,2,19,4,21,6,23,8,25,10,27,12,29,14,31,32,49,34,51,36,53,38,55,40,57,42,59,44,61,46,63],
    ![16,1,18,3,20,5,22,7,24,9,26,11,28,13,30,15,48,33,50,35,52,37,54,39,56,41,58,43,60,45,62,47],
    ![0,33,2,35,4,37,6,39,8,41,10,43,12,45,14,47,16,49,18,51,20,53,22,55,24,57,26,59,28,61,30,63],
    ![32,1,34,3,36,5,38,7,40,9,42,11,44,13,46,15,48,17,50,19,52,21,54,23,56,25,58,27,60,29,62,31],
    ![0,6,1,7,8,14,9,15,16,22,17,23,24,30,25,31,32,38,33,39,40,46,41,47,48,54,49,55,56,62,57,63],
    ![4,2,5,3,12,10,13,11,20,18,21,19,28,26,29,27,36,34,37,35,44,42,45,43,52,50,53,51,60,58,61,59],
    ![0,10,1,11,4,14,5,15,16,26,17,27,20,30,21,31,32,42,33,43,36,46,37,47,48,58,49,59,52,62,53,63],
    ![8,2,9,3,12,6,13,7,24,18,25,19,28,22,29,23,40,34,41,35,44,38,45,39,56,50,57,51,60,54,61,55],
    ![0,18,1,19,4,22,5,23,8,26,9,27,12,30,13,31,32,50,33,51,36,54,37,55,40,58,41,59,44,62,45,63],
    ![16,2,17,3,20,6,21,7,24,10,25,11,28,14,29,15,48,34,49,35,52,38,53,39,56,42,57,43,60,46,61,47],
    ![0,34,1,35,4,38,5,39,8,42,9,43,12,46,13,47,16,50,17,51,20,54,21,55,24,58,25,59,28,62,29,63],
    ![32,2,33,3,36,6,37,7,40,10,41,11,44,14,45,15,48,18,49,19,52,22,53,23,56,26,57,27,60,30,61,31],
    ![0,12,1,13,2,14,3,15,16,28,17,29,18,30,19,31,32,44,33,45,34,46,35,47,48,60,49,61,50,62,51,63],
    ![8,4,9,5,10,6,11,7,24,20,25,21,26,22,27,23,40,36,41,37,42,38,43,39,56,52,57,53,58,54,59,55],
    ![0,20,1,21,2,22,3,23,8,28,9,29,10,30,11,31,32,52,33,53,34,54,35,55,40,60,41,61,42,62,43,63],
    ![16,4,17,5,18,6,19,7,24,12,25,13,26,14,27,15,48,36,49,37,50,38,51,39,56,44,57,45,58,46,59,47],
    ![0,36,1,37,2,38,3,39,8,44,9,45,10,46,11,47,16,52,17,53,18,54,19,55,24,60,25,61,26,62,27,63],
    ![32,4,33,5,34,6,35,7,40,12,41,13,42,14,43,15,48,20,49,21,50,22,51,23,56,28,57,29,58,30,59,31],
    ![0,24,1,25,2,26,3,27,4,28,5,29,6,30,7,31,32,56,33,57,34,58,35,59,36,60,37,61,38,62,39,63],
    ![16,8,17,9,18,10,19,11,20,12,21,13,22,14,23,15,48,40,49,41,50,42,51,43,52,44,53,45,54,46,55,47],
    ![0,40,1,41,2,42,3,43,4,44,5,45,6,46,7,47,16,56,17,57,18,58,19,59,20,60,21,61,22,62,23,63],
    ![32,8,33,9,34,10,35,11,36,12,37,13,38,14,39,15,48,24,49,25,50,26,51,27,52,28,53,29,54,30,55,31],
    ![0,48,1,49,2,50,3,51,4,52,5,53,6,54,7,55,8,56,9,57,10,58,11,59,12,60,13,61,14,62,15,63],
    ![32,16,33,17,34,18,35,19,36,20,37,21,38,22,39,23,40,24,41,25,42,26,43,27,44,28,45,29,46,30,47,31]]

def cardSupport : Fin 12→List (Fin 16) :=
  ![[0,3,12,15],
    [4,7,8,11],
    [1,2,13,14],
    [5,6,9,10],
    [0,5,10,15],
    [2,7,8,13],
    [1,4,11,14],
    [3,6,9,12],
    [0,6,9,15],
    [2,4,11,13],
    [1,7,8,14],
    [3,5,10,12]]

def targetSupport : Fin 15→List (Fin 64) :=
  ![[0,3,12,15,48,51,60,63],
    [0,3,20,23,40,43,60,63],
    [0,3,24,27,36,39,60,63],
    [0,5,10,15,48,53,58,63],
    [0,5,18,23,40,45,58,63],
    [0,5,24,29,34,39,58,63],
    [0,6,9,15,48,54,57,63],
    [0,9,18,27,36,45,54,63],
    [0,9,20,29,34,43,54,63],
    [0,6,17,23,40,46,57,63],
    [0,10,17,27,36,46,53,63],
    [0,12,17,29,34,46,51,63],
    [0,6,24,30,33,39,57,63],
    [0,10,20,30,33,43,53,63],
    [0,12,18,30,33,45,51,63]]

def card (c : Fin 30) (w : Fin 16) : IRow 64 := fun i=>
  (if i=inputTable c ⟨2*w.val,by omega⟩ then 1 else 0)+
  (if i=inputTable c ⟨2*w.val+1,by omega⟩ then 1 else 0)
def line (j : Fin 12) (w : Fin 16) : GZ := if w∈cardSupport j then 1 else 0
def pivot : Fin 12→Fin 16 := ![0,4,1,5,0,2,1,3,0,2,1,3]
def target (j : Fin 15) (w : Fin 64) : GZ := if w∈targetSupport j then 1 else 0

def problem : IntegerCertificate.Problem 64 64 16 30 12 15 where
  tensor := IntegerCertificate.unitRow
  cards := card
  cardLines := line
  cardPivot := pivot
  targets := target
  targetPivot _ := 0
  live i := decide (i=0)

abbrev Rows := List (IRow 64)
def Covers (rows : Rows) : Prop := ∀scale : Fin 64→ℂ,
  Satisfies (mapRows rows) scale → problem.toProblem.Live scale →
  problem.toProblem.SafeCards scale → problem.toProblem.Accepted scale

theorem covers_dead (rows : Rows) (w : IntegerCertificate.Witness)
    (hc : IntegerCertificate.checkRow rows (IntegerCertificate.unitRow 0) w=true) : Covers rows := by
  exact IntegerCertificate.Certificate.sound problem (.dead 0 w) rows (by simpa [IntegerCertificate.Certificate.check,problem] using hc)

theorem covers_target (rows : Rows) (j : Fin 15) (w : Fin 64→IntegerCertificate.Witness)
    (hc : ∀i,IntegerCertificate.checkRow rows
      (IntegerCertificate.wedgeRow problem.tensor (problem.targets j) (problem.targetPivot j) i) (w i)=true) : Covers rows := by
  apply IntegerCertificate.Certificate.sound problem (.product j w) rows
  change (decide (target j 0 ≠ 0) && decide (∀ i : Fin 64,
    IntegerCertificate.checkRow rows (IntegerCertificate.wedgeRow problem.tensor
      (problem.targets j) (problem.targetPivot j) i) (w i) = true)) = true
  have hpall : ∀ k : Fin 15, target k 0 ≠ 0 := by decide +kernel
  have hp := hpall j
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hp, decide_eq_true hc⟩

theorem covers_split (rows : Rows) (c : Fin 30) (reductions : Fin 12→IntegerCertificate.Reduction 64)
    (hc : ∀j,(reductions j).check (rows++IntegerCertificate.wedgeRows (problem.cards c)
      (problem.cardLines j) (problem.cardPivot j))=true)
    (children : ∀j,Covers (reductions j).rows) : Covers rows := by
  intro scale hr hl hs
  obtain ⟨j,t,he⟩ := hs c
  have added : Satisfies (mapRows (rows++IntegerCertificate.wedgeRows (problem.cards c)
      (problem.cardLines j) (problem.cardPivot j))) scale := by
    rw [mapRows,List.map_append]
    change Satisfies (mapRows rows++mapRows (IntegerCertificate.wedgeRows _ _ _)) scale
    rw [IntegerCertificate.map_wedgeRows]
    exact (LinearCertificate.satisfies_append _ _ _).mpr
      ⟨hr,LinearCertificate.line_implies_wedgeRows _ _ _ _ t he⟩
  exact children j scale ((reductions j).sound _ (hc j) added) hl hs

theorem covers_zero : Covers [IntegerCertificate.unitRow 0] := by
  apply covers_dead _ { denominator := 1, weights := [(0,1)] }
  decide +kernel

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SixPortProblem
end
