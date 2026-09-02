default Order dec

union tree = {
  Leaf : int,
  Branch : (tree, tree)
}

$[sv_module { stdout = true }]
val "print_endline" : string -> unit

function left(tree : tree) -> tree = match tree {
  Branch((child, _)) => child,
  Leaf(_) => tree
}

function describe(tree : tree) -> string = match tree {
  Branch(_) => "branch",
  Leaf(_) => "leaf"
}

function main(() : unit) -> unit = {
  let tree = Branch((Leaf(1), Leaf(2)));
  print_endline(describe(tree));
  print_endline(describe(left(tree)))
}
