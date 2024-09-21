import Lake
open Lake DSL

package «snippets» where
  -- add package configuration options here

lean_lib «Snippets» where
  -- add library configuration options here

@[default_target]
lean_exe «snippets» where
  root := `Main
