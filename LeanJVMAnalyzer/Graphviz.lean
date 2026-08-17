import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.HtmlDisplay
import Lean.Server.Rpc.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

open ProofWidgets Jsx

structure Graphviz.Widget.Props where
  dot : String
  deriving Lean.Server.RpcEncodable

@[widget_module]
def Graphviz.Widget : Component Graphviz.Widget.Props where
  javascript := "
import * as React from 'react';
const e = React.createElement;
import { useRpcSession, RpcContext, InteractiveCode, useAsync, mapRpcError } from '@leanprover/infoview';
import * as Viz from 'https://esm.run/@viz-js/viz';

const MarkingContext = React.createContext({});

export default function(props) {
  const [globalState, setGlobalState] = React.useState(props.kind?.Context?.state);
  const rs = React.useContext(RpcContext);

  const ref = React.useRef(null)

  React.useEffect(() => {
    Viz.instance().then(viz => {
      const svg = viz.renderSVGElement(props.dot)
      ref.current.innerHTML = ''
      ref.current.appendChild(svg)
    }).catch(e => setDebug(JSON.stringify(e.toString())))
  }, [props.dot])

  return e('div', { ref })
}
"

def Lean.SourceInfo.mkCanonical : SourceInfo → SourceInfo
  | .synthetic s e _ => .synthetic s e true
  | si => si

def Lean.Syntax.mkInfoCanonical : Syntax → Syntax
  | .missing => .missing
  | .node i k a => .node i.mkCanonical k a
  | .atom i v => .atom i.mkCanonical v
  | .ident i r v p => .ident i.mkCanonical r v p

def Lean.TSyntax.mkInfoCanonical {k} : TSyntax k → TSyntax k :=
  (.mk ·.raw.mkInfoCanonical)

class Graphviz.ToDot (α : Type*) (β : outParam Type*) [Inhabited β] where
  dot : α → β → String

instance : Graphviz.ToDot String Unit := ⟨fun s _ ↦ s⟩

macro "#graphviz " dot:term : command =>
  Lean.TSyntax.mkInfoCanonical <$> `(#html do return <Graphviz.Widget dot={Graphviz.ToDot.dot (← $dot) default} />)
macro "#graphviz[" opts:term "] " dot:term : command =>
  Lean.TSyntax.mkInfoCanonical <$> `(#html <Graphviz.Widget dot={Graphviz.ToDot.dot $dot $opts} />)

#graphviz pure (f := IO) "digraph { a -> b }"
