import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortOrbitWitness

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def irep0320State : DirectionTriple := ![some (directionEquiv 1),none,none]

def irep0320Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0320Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0320Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0320Node0Reductions irep0320Node0Children

theorem irep0320_cached_checked :
    irep0320Node0.check (cachedIntegerProblem irep0320State) (integerInitialRows irep0320State) = true := by
  decide +kernel

theorem irep0320_checked :
    irep0320Node0.check (integerProblem irep0320State) (integerInitialRows irep0320State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0320_cached_checked

theorem irep0320_solved : Solved irep0320State :=
  solved_of_integer_certificate irep0320State irep0320Node0 irep0320_checked

theorem irep0320_representative : Solved (stateEquiv (representativeCode 320)) := by
  have he : stateEquiv (representativeCode 320) = irep0320State := by decide +kernel
  rw [he]
  exact irep0320_solved

def irep0321State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 0)]

def irep0321Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0321Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0321Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0321Node0Reductions irep0321Node0Children

theorem irep0321_cached_checked :
    irep0321Node0.check (cachedIntegerProblem irep0321State) (integerInitialRows irep0321State) = true := by
  decide +kernel

theorem irep0321_checked :
    irep0321Node0.check (integerProblem irep0321State) (integerInitialRows irep0321State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0321_cached_checked

theorem irep0321_solved : Solved irep0321State :=
  solved_of_integer_certificate irep0321State irep0321Node0 irep0321_checked

theorem irep0321_representative : Solved (stateEquiv (representativeCode 321)) := by
  have he : stateEquiv (representativeCode 321) = irep0321State := by decide +kernel
  rw [he]
  exact irep0321_solved

def irep0322State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 1)]

def irep0322Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0322Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0322Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0322Node0Reductions irep0322Node0Children

theorem irep0322_cached_checked :
    irep0322Node0.check (cachedIntegerProblem irep0322State) (integerInitialRows irep0322State) = true := by
  decide +kernel

theorem irep0322_checked :
    irep0322Node0.check (integerProblem irep0322State) (integerInitialRows irep0322State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0322_cached_checked

theorem irep0322_solved : Solved irep0322State :=
  solved_of_integer_certificate irep0322State irep0322Node0 irep0322_checked

theorem irep0322_representative : Solved (stateEquiv (representativeCode 322)) := by
  have he : stateEquiv (representativeCode 322) = irep0322State := by decide +kernel
  rw [he]
  exact irep0322_solved

def irep0323State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 2)]

def irep0323Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0323Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0323Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0323Node0Reductions irep0323Node0Children

theorem irep0323_cached_checked :
    irep0323Node0.check (cachedIntegerProblem irep0323State) (integerInitialRows irep0323State) = true := by
  decide +kernel

theorem irep0323_checked :
    irep0323Node0.check (integerProblem irep0323State) (integerInitialRows irep0323State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0323_cached_checked

theorem irep0323_solved : Solved irep0323State :=
  solved_of_integer_certificate irep0323State irep0323Node0 irep0323_checked

theorem irep0323_representative : Solved (stateEquiv (representativeCode 323)) := by
  have he : stateEquiv (representativeCode 323) = irep0323State := by decide +kernel
  rw [he]
  exact irep0323_solved

def irep0324State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 4)]

def irep0324Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0324Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0324Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0324Node0Reductions irep0324Node0Children

theorem irep0324_cached_checked :
    irep0324Node0.check (cachedIntegerProblem irep0324State) (integerInitialRows irep0324State) = true := by
  decide +kernel

theorem irep0324_checked :
    irep0324Node0.check (integerProblem irep0324State) (integerInitialRows irep0324State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0324_cached_checked

theorem irep0324_solved : Solved irep0324State :=
  solved_of_integer_certificate irep0324State irep0324Node0 irep0324_checked

theorem irep0324_representative : Solved (stateEquiv (representativeCode 324)) := by
  have he : stateEquiv (representativeCode 324) = irep0324State := by decide +kernel
  rw [he]
  exact irep0324_solved

def irep0325State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 5)]

def irep0325Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ)),(10,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ)),(10,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0325Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0325Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0325Node0Reductions irep0325Node0Children

theorem irep0325_cached_checked :
    irep0325Node0.check (cachedIntegerProblem irep0325State) (integerInitialRows irep0325State) = true := by
  decide +kernel

theorem irep0325_checked :
    irep0325Node0.check (integerProblem irep0325State) (integerInitialRows irep0325State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0325_cached_checked

theorem irep0325_solved : Solved irep0325State :=
  solved_of_integer_certificate irep0325State irep0325Node0 irep0325_checked

theorem irep0325_representative : Solved (stateEquiv (representativeCode 325)) := by
  have he : stateEquiv (representativeCode 325) = irep0325State := by decide +kernel
  rw [he]
  exact irep0325_solved

def irep0326State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 6)]

def irep0326Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0326Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0326Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0326Node0Reductions irep0326Node0Children

theorem irep0326_cached_checked :
    irep0326Node0.check (cachedIntegerProblem irep0326State) (integerInitialRows irep0326State) = true := by
  decide +kernel

theorem irep0326_checked :
    irep0326Node0.check (integerProblem irep0326State) (integerInitialRows irep0326State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0326_cached_checked

theorem irep0326_solved : Solved irep0326State :=
  solved_of_integer_certificate irep0326State irep0326Node0 irep0326_checked

theorem irep0326_representative : Solved (stateEquiv (representativeCode 326)) := by
  have he : stateEquiv (representativeCode 326) = irep0326State := by decide +kernel
  rw [he]
  exact irep0326_solved

def irep0327State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 8)]

def irep0327Node3Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(0,(⟨(2),(0)⟩ : GZ)),(3,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0327Node3Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 0 { denominator := 1, weights := [(0,1)] },
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
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
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

def irep0327Node3 : Certificate 4 64 60 48 960 :=
  .split 5 irep0327Node3Reductions irep0327Node3Children

def irep0327Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,(⟨(2),(0)⟩ : GZ)],![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] },{ denominator := 1, weights := [(2,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0327Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] },
    irep0327Node3,
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
    .dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 1 { denominator := 1, weights := [(0,1)] }]

def irep0327Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0327Node0Reductions irep0327Node0Children

theorem irep0327_cached_checked :
    irep0327Node0.check (cachedIntegerProblem irep0327State) (integerInitialRows irep0327State) = true := by
  decide +kernel

theorem irep0327_checked :
    irep0327Node0.check (integerProblem irep0327State) (integerInitialRows irep0327State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0327_cached_checked

theorem irep0327_solved : Solved irep0327State :=
  solved_of_integer_certificate irep0327State irep0327Node0 irep0327_checked

theorem irep0327_representative : Solved (stateEquiv (representativeCode 327)) := by
  have he : stateEquiv (representativeCode 327) = irep0327State := by decide +kernel
  rw [he]
  exact irep0327_solved

def irep0328State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 9)]

def irep0328Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,1),(12,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,1),(12,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0328Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0328Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0328Node0Reductions irep0328Node0Children

theorem irep0328_cached_checked :
    irep0328Node0.check (cachedIntegerProblem irep0328State) (integerInitialRows irep0328State) = true := by
  decide +kernel

theorem irep0328_checked :
    irep0328Node0.check (integerProblem irep0328State) (integerInitialRows irep0328State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0328_cached_checked

theorem irep0328_solved : Solved irep0328State :=
  solved_of_integer_certificate irep0328State irep0328Node0 irep0328_checked

theorem irep0328_representative : Solved (stateEquiv (representativeCode 328)) := by
  have he : stateEquiv (representativeCode 328) = irep0328State := by decide +kernel
  rw [he]
  exact irep0328_solved

def irep0329State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 10)]

def irep0329Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(16,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0329Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0329Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0329Node0Reductions irep0329Node0Children

theorem irep0329_cached_checked :
    irep0329Node0.check (cachedIntegerProblem irep0329State) (integerInitialRows irep0329State) = true := by
  decide +kernel

theorem irep0329_checked :
    irep0329Node0.check (integerProblem irep0329State) (integerInitialRows irep0329State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0329_cached_checked

theorem irep0329_solved : Solved irep0329State :=
  solved_of_integer_certificate irep0329State irep0329Node0 irep0329_checked

theorem irep0329_representative : Solved (stateEquiv (representativeCode 329)) := by
  have he : stateEquiv (representativeCode 329) = irep0329State := by decide +kernel
  rw [he]
  exact irep0329_solved

def irep0330State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 16)]

def irep0330Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0330Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0330Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0330Node0Reductions irep0330Node0Children

theorem irep0330_cached_checked :
    irep0330Node0.check (cachedIntegerProblem irep0330State) (integerInitialRows irep0330State) = true := by
  decide +kernel

theorem irep0330_checked :
    irep0330Node0.check (integerProblem irep0330State) (integerInitialRows irep0330State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0330_cached_checked

theorem irep0330_solved : Solved irep0330State :=
  solved_of_integer_certificate irep0330State irep0330Node0 irep0330_checked

theorem irep0330_representative : Solved (stateEquiv (representativeCode 330)) := by
  have he : stateEquiv (representativeCode 330) = irep0330State := by decide +kernel
  rw [he]
  exact irep0330_solved

def irep0331State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 17)]

def irep0331Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,1),(9,(⟨(0),(1)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0331Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0331Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0331Node0Reductions irep0331Node0Children

theorem irep0331_cached_checked :
    irep0331Node0.check (cachedIntegerProblem irep0331State) (integerInitialRows irep0331State) = true := by
  decide +kernel

theorem irep0331_checked :
    irep0331Node0.check (integerProblem irep0331State) (integerInitialRows irep0331State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0331_cached_checked

theorem irep0331_solved : Solved irep0331State :=
  solved_of_integer_certificate irep0331State irep0331Node0 irep0331_checked

theorem irep0331_representative : Solved (stateEquiv (representativeCode 331)) := by
  have he : stateEquiv (representativeCode 331) = irep0331State := by decide +kernel
  rw [he]
  exact irep0331_solved

def irep0332State : DirectionTriple := ![some (directionEquiv 1),none,some (directionEquiv 18)]

def irep0332Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0332Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0332Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0332Node0Reductions irep0332Node0Children

theorem irep0332_cached_checked :
    irep0332Node0.check (cachedIntegerProblem irep0332State) (integerInitialRows irep0332State) = true := by
  decide +kernel

theorem irep0332_checked :
    irep0332Node0.check (integerProblem irep0332State) (integerInitialRows irep0332State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0332_cached_checked

theorem irep0332_solved : Solved irep0332State :=
  solved_of_integer_certificate irep0332State irep0332Node0 irep0332_checked

theorem irep0332_representative : Solved (stateEquiv (representativeCode 332)) := by
  have he : stateEquiv (representativeCode 332) = irep0332State := by decide +kernel
  rw [he]
  exact irep0332_solved

def irep0333State : DirectionTriple := ![some (directionEquiv 1),some (directionEquiv 0),none]

def irep0333Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0333Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0333Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0333Node0Reductions irep0333Node0Children

theorem irep0333_cached_checked :
    irep0333Node0.check (cachedIntegerProblem irep0333State) (integerInitialRows irep0333State) = true := by
  decide +kernel

theorem irep0333_checked :
    irep0333Node0.check (integerProblem irep0333State) (integerInitialRows irep0333State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0333_cached_checked

theorem irep0333_solved : Solved irep0333State :=
  solved_of_integer_certificate irep0333State irep0333Node0 irep0333_checked

theorem irep0333_representative : Solved (stateEquiv (representativeCode 333)) := by
  have he : stateEquiv (representativeCode 333) = irep0333State := by decide +kernel
  rw [he]
  exact irep0333_solved

def irep0334State : DirectionTriple := ![some (directionEquiv 1),some (directionEquiv 0),some (directionEquiv 0)]

def irep0334Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
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
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(9,(⟨(-1),(0)⟩ : GZ)),(10,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(9,1),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0334Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0334Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0334Node0Reductions irep0334Node0Children

theorem irep0334_cached_checked :
    irep0334Node0.check (cachedIntegerProblem irep0334State) (integerInitialRows irep0334State) = true := by
  decide +kernel

theorem irep0334_checked :
    irep0334Node0.check (integerProblem irep0334State) (integerInitialRows irep0334State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0334_cached_checked

theorem irep0334_solved : Solved irep0334State :=
  solved_of_integer_certificate irep0334State irep0334Node0 irep0334_checked

theorem irep0334_representative : Solved (stateEquiv (representativeCode 334)) := by
  have he : stateEquiv (representativeCode 334) = irep0334State := by decide +kernel
  rw [he]
  exact irep0334_solved

def irep0335State : DirectionTriple := ![some (directionEquiv 1),some (directionEquiv 0),some (directionEquiv 1)]

def irep0335Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(2),(0)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def irep0335Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
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

def irep0335Node0 : Certificate 4 64 60 48 960 :=
  .split 4 irep0335Node0Reductions irep0335Node0Children

theorem irep0335_cached_checked :
    irep0335Node0.check (cachedIntegerProblem irep0335State) (integerInitialRows irep0335State) = true := by
  decide +kernel

theorem irep0335_checked :
    irep0335Node0.check (integerProblem irep0335State) (integerInitialRows irep0335State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact irep0335_cached_checked

theorem irep0335_solved : Solved irep0335State :=
  solved_of_integer_certificate irep0335State irep0335Node0 irep0335_checked

theorem irep0335_representative : Solved (stateEquiv (representativeCode 335)) := by
  have he : stateEquiv (representativeCode 335) = irep0335State := by decide +kernel
  rw [he]
  exact irep0335_solved

theorem representativeBatch020 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (Fin.ofNat 4045 (16*20+i.val)))) := by
  fin_cases i
  · exact irep0320_representative
  · exact irep0321_representative
  · exact irep0322_representative
  · exact irep0323_representative
  · exact irep0324_representative
  · exact irep0325_representative
  · exact irep0326_representative
  · exact irep0327_representative
  · exact irep0328_representative
  · exact irep0329_representative
  · exact irep0330_representative
  · exact irep0331_representative
  · exact irep0332_representative
  · exact irep0333_representative
  · exact irep0334_representative
  · exact irep0335_representative

end
end Holant.Pauli.ExoticKlein.SixPort
