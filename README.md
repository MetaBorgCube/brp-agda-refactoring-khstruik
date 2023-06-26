# Refactoring with Confidence - Creating and proving the correctness of a refactoring to add arguments to a function in a functional language 

> This thesis was part of the 2022/2023 edition of the
[CSE3000 (Bsc Research Project)](https://cse3000-research-project.github.io/2023/Q4)
course at Delft University of Technology.

This repository contains the source code for my bachelor thesis on
correct-by-construction of functional code. Specifically, my focus was on creating,
and proving the correctness of, a refactoring to add a new argument to a function
definition and updating its call sites to include the default value for this
argument. An example of the desired effects of this refactoring can be seen
below.


```haskell
-- Before the refactoring is applied

add :: Int -> Int -> Int
add a b = a + b

...

add 1 2 -- Returns 3

-- After the refactoring is applied with a default argument value of 0

add :: Int -> Int -> Int -> Int
add a b c = a + b

...

add 1 2 0 -- Still returns 3
```

## Versions of software used
This project was originally compiled with version **2.6.3** of the Agda compiler.
The version of the Agda standard library used is added as a git submodule to this
repository.

## Cloning repository
When clone this repository locally make sure to clone with submodules, otherwise
the Agda standard library will not be downloaded.
```bash
git clone --recurse-submodules https://github.com/MetaBorgCube/brp-agda-refactoring-khstruik.git
```

## License
This source code is licensed under the MIT license. The full license text is
available in the [LICENSE.md](https://github.com/MetaBorgCube/brp-agda-refactoring-khstruik/LICENSE.md) file

