import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortAnchorWitness

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def arep0623State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 1),some (directionEquiv 19)]

def arep0623Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ)),(10,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0623Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0623Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0623Node0Reductions arep0623Node0Children

theorem arep0623_cached_checked :
    arep0623Node0.check (cachedIntegerProblem arep0623State) (integerInitialRows arep0623State) = true := by
  decide +kernel

theorem arep0623_checked :
    arep0623Node0.check (integerProblem arep0623State) (integerInitialRows arep0623State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0623_cached_checked

theorem arep0623_solved : Solved arep0623State :=
  solved_of_integer_certificate arep0623State arep0623Node0 arep0623_checked

theorem arep0623_representative : Solved (stateEquiv (representativeCode 623)) := by
  have he : stateEquiv (representativeCode 623) = arep0623State := by decide +kernel
  rw [he]
  exact arep0623_solved

theorem anchorEntry0384_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 384))) := by
  have he : anchorRepresentative 384 = 623 := by decide +kernel
  rw [he]
  exact arep0623_representative

def arep0627State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 2)]

def arep0627Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(2)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(2)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0627Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0627Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0627Node0Reductions arep0627Node0Children

theorem arep0627_cached_checked :
    arep0627Node0.check (cachedIntegerProblem arep0627State) (integerInitialRows arep0627State) = true := by
  decide +kernel

theorem arep0627_checked :
    arep0627Node0.check (integerProblem arep0627State) (integerInitialRows arep0627State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0627_cached_checked

theorem arep0627_solved : Solved arep0627State :=
  solved_of_integer_certificate arep0627State arep0627Node0 arep0627_checked

theorem arep0627_representative : Solved (stateEquiv (representativeCode 627)) := by
  have he : stateEquiv (representativeCode 627) = arep0627State := by decide +kernel
  rw [he]
  exact arep0627_solved

theorem anchorEntry0385_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 385))) := by
  have he : anchorRepresentative 385 = 627 := by decide +kernel
  rw [he]
  exact arep0627_representative

def arep0628State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 3)]

def arep0628Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0628Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0628Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0628Node0Reductions arep0628Node0Children

theorem arep0628_cached_checked :
    arep0628Node0.check (cachedIntegerProblem arep0628State) (integerInitialRows arep0628State) = true := by
  decide +kernel

theorem arep0628_checked :
    arep0628Node0.check (integerProblem arep0628State) (integerInitialRows arep0628State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0628_cached_checked

theorem arep0628_solved : Solved arep0628State :=
  solved_of_integer_certificate arep0628State arep0628Node0 arep0628_checked

theorem arep0628_representative : Solved (stateEquiv (representativeCode 628)) := by
  have he : stateEquiv (representativeCode 628) = arep0628State := by decide +kernel
  rw [he]
  exact arep0628_solved

theorem anchorEntry0386_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 386))) := by
  have he : anchorRepresentative 386 = 628 := by decide +kernel
  rw [he]
  exact arep0628_representative

def arep0629State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 4)]

def arep0629Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0629Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0629Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0629Node0Reductions arep0629Node0Children

theorem arep0629_cached_checked :
    arep0629Node0.check (cachedIntegerProblem arep0629State) (integerInitialRows arep0629State) = true := by
  decide +kernel

theorem arep0629_checked :
    arep0629Node0.check (integerProblem arep0629State) (integerInitialRows arep0629State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0629_cached_checked

theorem arep0629_solved : Solved arep0629State :=
  solved_of_integer_certificate arep0629State arep0629Node0 arep0629_checked

theorem arep0629_representative : Solved (stateEquiv (representativeCode 629)) := by
  have he : stateEquiv (representativeCode 629) = arep0629State := by decide +kernel
  rw [he]
  exact arep0629_solved

theorem anchorEntry0387_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 387))) := by
  have he : anchorRepresentative 387 = 629 := by decide +kernel
  rw [he]
  exact arep0629_representative

def arep0630State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 5)]

def arep0630Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-4)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0630Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0630Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0630Node0Reductions arep0630Node0Children

theorem arep0630_cached_checked :
    arep0630Node0.check (cachedIntegerProblem arep0630State) (integerInitialRows arep0630State) = true := by
  decide +kernel

theorem arep0630_checked :
    arep0630Node0.check (integerProblem arep0630State) (integerInitialRows arep0630State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0630_cached_checked

theorem arep0630_solved : Solved arep0630State :=
  solved_of_integer_certificate arep0630State arep0630Node0 arep0630_checked

theorem arep0630_representative : Solved (stateEquiv (representativeCode 630)) := by
  have he : stateEquiv (representativeCode 630) = arep0630State := by decide +kernel
  rw [he]
  exact arep0630_solved

theorem anchorEntry0388_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 388))) := by
  have he : anchorRepresentative 388 = 630 := by decide +kernel
  rw [he]
  exact arep0630_representative

def arep0631State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 6)]

def arep0631Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0631Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0631Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0631Node0Reductions arep0631Node0Children

theorem arep0631_cached_checked :
    arep0631Node0.check (cachedIntegerProblem arep0631State) (integerInitialRows arep0631State) = true := by
  decide +kernel

theorem arep0631_checked :
    arep0631Node0.check (integerProblem arep0631State) (integerInitialRows arep0631State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0631_cached_checked

theorem arep0631_solved : Solved arep0631State :=
  solved_of_integer_certificate arep0631State arep0631Node0 arep0631_checked

theorem arep0631_representative : Solved (stateEquiv (representativeCode 631)) := by
  have he : stateEquiv (representativeCode 631) = arep0631State := by decide +kernel
  rw [he]
  exact arep0631_solved

theorem anchorEntry0389_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 389))) := by
  have he : anchorRepresentative 389 = 631 := by decide +kernel
  rw [he]
  exact arep0631_representative

def arep0632State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 7)]

def arep0632Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0632Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0632Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0632Node0Reductions arep0632Node0Children

theorem arep0632_cached_checked :
    arep0632Node0.check (cachedIntegerProblem arep0632State) (integerInitialRows arep0632State) = true := by
  decide +kernel

theorem arep0632_checked :
    arep0632Node0.check (integerProblem arep0632State) (integerInitialRows arep0632State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0632_cached_checked

theorem arep0632_solved : Solved arep0632State :=
  solved_of_integer_certificate arep0632State arep0632Node0 arep0632_checked

theorem arep0632_representative : Solved (stateEquiv (representativeCode 632)) := by
  have he : stateEquiv (representativeCode 632) = arep0632State := by decide +kernel
  rw [he]
  exact arep0632_solved

theorem anchorEntry0390_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 390))) := by
  have he : anchorRepresentative 390 = 632 := by decide +kernel
  rw [he]
  exact arep0632_representative

def arep0633State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 8)]

def arep0633Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0633Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] }]

def arep0633Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0633Node0Reductions arep0633Node0Children

theorem arep0633_cached_checked :
    arep0633Node0.check (cachedIntegerProblem arep0633State) (integerInitialRows arep0633State) = true := by
  decide +kernel

theorem arep0633_checked :
    arep0633Node0.check (integerProblem arep0633State) (integerInitialRows arep0633State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0633_cached_checked

theorem arep0633_solved : Solved arep0633State :=
  solved_of_integer_certificate arep0633State arep0633Node0 arep0633_checked

theorem arep0633_representative : Solved (stateEquiv (representativeCode 633)) := by
  have he : stateEquiv (representativeCode 633) = arep0633State := by decide +kernel
  rw [he]
  exact arep0633_solved

theorem anchorEntry0391_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 391))) := by
  have he : anchorRepresentative 391 = 633 := by decide +kernel
  rw [he]
  exact arep0633_representative

def arep0634State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 9)]

def arep0634Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,1),(12,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,1),(12,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-4)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-3),(0)⟩ : GZ)),(6,(⟨(3),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(11,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(4)⟩ : GZ)),(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(11,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(6,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0634Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0634Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0634Node0Reductions arep0634Node0Children

theorem arep0634_cached_checked :
    arep0634Node0.check (cachedIntegerProblem arep0634State) (integerInitialRows arep0634State) = true := by
  decide +kernel

theorem arep0634_checked :
    arep0634Node0.check (integerProblem arep0634State) (integerInitialRows arep0634State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0634_cached_checked

theorem arep0634_solved : Solved arep0634State :=
  solved_of_integer_certificate arep0634State arep0634Node0 arep0634_checked

theorem arep0634_representative : Solved (stateEquiv (representativeCode 634)) := by
  have he : stateEquiv (representativeCode 634) = arep0634State := by decide +kernel
  rw [he]
  exact arep0634_solved

theorem anchorEntry0392_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 392))) := by
  have he : anchorRepresentative 392 = 634 := by decide +kernel
  rw [he]
  exact arep0634_representative

def arep0635State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 10)]

def arep0635Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(16,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(4),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(11,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0635Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0635Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0635Node0Reductions arep0635Node0Children

theorem arep0635_cached_checked :
    arep0635Node0.check (cachedIntegerProblem arep0635State) (integerInitialRows arep0635State) = true := by
  decide +kernel

theorem arep0635_checked :
    arep0635Node0.check (integerProblem arep0635State) (integerInitialRows arep0635State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0635_cached_checked

theorem arep0635_solved : Solved arep0635State :=
  solved_of_integer_certificate arep0635State arep0635Node0 arep0635_checked

theorem arep0635_representative : Solved (stateEquiv (representativeCode 635)) := by
  have he : stateEquiv (representativeCode 635) = arep0635State := by decide +kernel
  rw [he]
  exact arep0635_solved

theorem anchorEntry0393_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 393))) := by
  have he : anchorRepresentative 393 = 635 := by decide +kernel
  rw [he]
  exact arep0635_representative

def arep0636State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 11)]

def arep0636Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(16,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-4),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-2),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(-1),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(-1),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,(⟨(-1),(0)⟩ : GZ)),(11,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0636Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0636Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0636Node0Reductions arep0636Node0Children

theorem arep0636_cached_checked :
    arep0636Node0.check (cachedIntegerProblem arep0636State) (integerInitialRows arep0636State) = true := by
  decide +kernel

theorem arep0636_checked :
    arep0636Node0.check (integerProblem arep0636State) (integerInitialRows arep0636State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0636_cached_checked

theorem arep0636_solved : Solved arep0636State :=
  solved_of_integer_certificate arep0636State arep0636Node0 arep0636_checked

theorem arep0636_representative : Solved (stateEquiv (representativeCode 636)) := by
  have he : stateEquiv (representativeCode 636) = arep0636State := by decide +kernel
  rw [he]
  exact arep0636_solved

theorem anchorEntry0394_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 394))) := by
  have he : anchorRepresentative 394 = 636 := by decide +kernel
  rw [he]
  exact arep0636_representative

def arep0637State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 16)]

def arep0637Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 16, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-5)⟩ : GZ)),(8,(⟨(-4),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(7,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(4),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 14, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(5),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 16, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-5)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-3),(0)⟩ : GZ)),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(5)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(7,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(0),(2)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(4),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-2),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(7,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0637Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0637Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0637Node0Reductions arep0637Node0Children

theorem arep0637_cached_checked :
    arep0637Node0.check (cachedIntegerProblem arep0637State) (integerInitialRows arep0637State) = true := by
  decide +kernel

theorem arep0637_checked :
    arep0637Node0.check (integerProblem arep0637State) (integerInitialRows arep0637State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0637_cached_checked

theorem arep0637_solved : Solved arep0637State :=
  solved_of_integer_certificate arep0637State arep0637Node0 arep0637_checked

theorem arep0637_representative : Solved (stateEquiv (representativeCode 637)) := by
  have he : stateEquiv (representativeCode 637) = arep0637State := by decide +kernel
  rw [he]
  exact arep0637_solved

theorem anchorEntry0395_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 395))) := by
  have he : anchorRepresentative 395 = 637 := by decide +kernel
  rw [he]
  exact arep0637_representative

def arep0638State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 17)]

def arep0638Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ)),(10,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(4),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-4)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(4)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,1),(8,(⟨(-1),(0)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0638Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0638Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0638Node0Reductions arep0638Node0Children

theorem arep0638_cached_checked :
    arep0638Node0.check (cachedIntegerProblem arep0638State) (integerInitialRows arep0638State) = true := by
  decide +kernel

theorem arep0638_checked :
    arep0638Node0.check (integerProblem arep0638State) (integerInitialRows arep0638State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0638_cached_checked

theorem arep0638_solved : Solved arep0638State :=
  solved_of_integer_certificate arep0638State arep0638Node0 arep0638_checked

theorem arep0638_representative : Solved (stateEquiv (representativeCode 638)) := by
  have he : stateEquiv (representativeCode 638) = arep0638State := by decide +kernel
  rw [he]
  exact arep0638_solved

theorem anchorEntry0396_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 396))) := by
  have he : anchorRepresentative 396 = 638 := by decide +kernel
  rw [he]
  exact arep0638_representative

def arep0639State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 18)]

def arep0639Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0639Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0639Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0639Node0Reductions arep0639Node0Children

theorem arep0639_cached_checked :
    arep0639Node0.check (cachedIntegerProblem arep0639State) (integerInitialRows arep0639State) = true := by
  decide +kernel

theorem arep0639_checked :
    arep0639Node0.check (integerProblem arep0639State) (integerInitialRows arep0639State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0639_cached_checked

theorem arep0639_solved : Solved arep0639State :=
  solved_of_integer_certificate arep0639State arep0639Node0 arep0639_checked

theorem arep0639_representative : Solved (stateEquiv (representativeCode 639)) := by
  have he : stateEquiv (representativeCode 639) = arep0639State := by decide +kernel
  rw [he]
  exact arep0639_solved

theorem anchorEntry0397_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 397))) := by
  have he : anchorRepresentative 397 = 639 := by decide +kernel
  rw [he]
  exact arep0639_representative

def arep0640State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 2),some (directionEquiv 19)]

def arep0640Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-4),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(3)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0640Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0640Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0640Node0Reductions arep0640Node0Children

theorem arep0640_cached_checked :
    arep0640Node0.check (cachedIntegerProblem arep0640State) (integerInitialRows arep0640State) = true := by
  decide +kernel

theorem arep0640_checked :
    arep0640Node0.check (integerProblem arep0640State) (integerInitialRows arep0640State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0640_cached_checked

theorem arep0640_solved : Solved arep0640State :=
  solved_of_integer_certificate arep0640State arep0640Node0 arep0640_checked

theorem arep0640_representative : Solved (stateEquiv (representativeCode 640)) := by
  have he : stateEquiv (representativeCode 640) = arep0640State := by decide +kernel
  rw [he]
  exact arep0640_solved

theorem anchorEntry0398_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 398))) := by
  have he : anchorRepresentative 398 = 640 := by decide +kernel
  rw [he]
  exact arep0640_representative

def arep0645State : DirectionTriple := ![some (directionEquiv 2),some (directionEquiv 3),some (directionEquiv 3)]

def arep0645Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(7,(⟨(0),(2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(2)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(7,(⟨(0),(2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(2)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep0645Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep0645Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep0645Node0Reductions arep0645Node0Children

theorem arep0645_cached_checked :
    arep0645Node0.check (cachedIntegerProblem arep0645State) (integerInitialRows arep0645State) = true := by
  decide +kernel

theorem arep0645_checked :
    arep0645Node0.check (integerProblem arep0645State) (integerInitialRows arep0645State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep0645_cached_checked

theorem arep0645_solved : Solved arep0645State :=
  solved_of_integer_certificate arep0645State arep0645Node0 arep0645_checked

theorem arep0645_representative : Solved (stateEquiv (representativeCode 645)) := by
  have he : stateEquiv (representativeCode 645) = arep0645State := by decide +kernel
  rw [he]
  exact arep0645_solved

theorem anchorEntry0399_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 399))) := by
  have he : anchorRepresentative 399 = 645 := by decide +kernel
  rw [he]
  exact arep0645_representative

theorem anchorBatch024 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 (16*24+i.val))))) := by
  fin_cases i
  · exact anchorEntry0384_solved
  · exact anchorEntry0385_solved
  · exact anchorEntry0386_solved
  · exact anchorEntry0387_solved
  · exact anchorEntry0388_solved
  · exact anchorEntry0389_solved
  · exact anchorEntry0390_solved
  · exact anchorEntry0391_solved
  · exact anchorEntry0392_solved
  · exact anchorEntry0393_solved
  · exact anchorEntry0394_solved
  · exact anchorEntry0395_solved
  · exact anchorEntry0396_solved
  · exact anchorEntry0397_solved
  · exact anchorEntry0398_solved
  · exact anchorEntry0399_solved

end
end Holant.Pauli.ExoticKlein.SixPort
