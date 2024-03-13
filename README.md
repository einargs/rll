# rll

# Development Environment
Because I've adopted haskell.nix, I've switched away from using stack
to run commands, though I still use the stack.yaml file to define
the snapshot and some other things.

I do need to include hpack in my tools I guess? Or I can just run a stack
command and have it generate the thing, since I guess `stack-to-nix` will
if the cabal file was generated by something newer.

I don't want to switch entirely over to just using a cabal file and
figuring out how to deal with things like extra-deps.

## Haskell.nix
See: https://input-output-hk.github.io/haskell.nix/tutorials/getting-started-flakes.html

## Testing
To run via nix: `nix run .#rll:test:rll-test`

To run via cabal: `cabal test rll-test`
