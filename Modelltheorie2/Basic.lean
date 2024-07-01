import Lean
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Real.Basic

#check Valuation
#check ℚ
#check ℝ

def hello := "world"

open Lean Widget

@[widget_module]
def
helloWidget :
Widget.Module where
  javascript :=
"
    import * as React from 'react';
    export default function(props) {
      const name = props.name || 'world'
      return React.createElement('p', {}, name + '!')
    }"

#widget helloWidget
