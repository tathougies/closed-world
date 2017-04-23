# closed-world: Recover instances at run-time

Haskell's static type system is extremely flexible, but there are some
limitations. For example, lists must hold exactly one type of element. Of
course, you can get around this by creating a sum type to hold multiple types,
but if you're writing a library, your sum type can't be extended by users.
Another option in modern Haskell is to use a GADT to carry a type class
dictionary and type around, but, again, this doesn't allow library users to
define new type classes and instances.

Enter `closed-world`. Closed world is an extremely mischievous library that lets
you wrap up `instance` declarations into a `Universe`, a collection of instance
dictionaries and instance dictionary constructors. Then, as long as you have a
type with a `Typeable` instance, you can ask your `Universe` to see if it
contains a particular `instance` of that type, and, if so, to use that
constraint in an expression.

## Example

For example, `Data.ClosedWorld` defines the following type

```haskell
data MyDynamic where
    MyDynamic :: Typeable a => a -> MyDynamic
```

Now, a list of type `[MyDynamic]` can contain any value, so long as it has a
`Typeable` instance. However, since I don't know the actual type of any of the
`a`, you can't do anything interesting with the values (other than call `typeOf`
on them)...

```haskell
myList :: [MyDynamic]
myList = [ MyDynamic (1 :: Int)
         , MyDynamic ("hello world" :: String)
         , MyDynamic (("hello", 3) :: (String, Int))
         , MyDynamic (("hello", "world") :: (String, String))
         , MyDynamic (Nothing :: Maybe Int)
         , MyDynamic (Just 34 :: Maybe Int)
         , MyDynamic (Just ("hello, world", 4) :: Maybe (String, Int))
         , MyDynamic ([1,2,3,4,5] :: [Int])
         , MyDynamic (["hello", "world"] :: [String]) ]
```

Now, suppose I wanted to `show` all the values in `myList`. I can't do this
normally, unless I add `Show` to the constraints of the `MyDynamic` constructor.

Actually, with `closed-world` you can! First, let's define a `Universe`, a
collection of `Show` instances. You'll need `-XScopedTypeVariables` and
`-XTemplateHaskell`.

```haskell
import Data.ClosedWorld

showIntInstance :: Universe
showIntInstance = $(mkUniverse [d| instance Show Int |])
```

This uses the template haskell `mkUniverse` function to generate the `Universe`
for us. This is your best bet, as the actual definition of the `Universe` value
makes heavy use of `unsafeCoerce`.

Now, we can `fmap` over the list, and convert each value to a string, if we know
how. You'll need `-XTypeApplications`

```haskell
showMyDynamic :: Universe -> [MyDynamic] -> [Maybe String]
showMyDynamic u = fmap (\(MyDynamic (x :: a)) -> withHead @(Show a) u Nothing (Just $ show x))
```

Now, if we run `showMyDynamic showIntInstance myList` in GHCi, we get

```haskell
[Just "1",Nothing,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing]
```

Awesome! Our `Show Int` instance was recovered at run-time! Let's add more show
instances. Let's do the one for `Show String`.

Er.. hold on. `String ~ [Char]` and `Show [Char]` isn't a valid Haskell 98
instance. The `Show [Char]` instance comes from a combinator of the `Show Char`
instance and the `Show a => Show [a]` instance.

We know how to do the `Show Char` instance.

```haskell
showCharInstance :: Universe
showCharInstance = $(mkUniverse [d| instance Show Char |])
```

`Universe`s combine monoidally. Let's see what `showMyDynamic` says now.

```
*Data.ClosedWorld.TH Data.ClosedWorld Data.ClosedWorld.Base Data.ClosedWorld.TH> showMyDynamic (showIntInstance <> showCharInstance) myList
[Just "1",Nothing,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing,Nothing]
```

Hmm... We need to add the instance for `Show a => Show [a]` to our universe too. Let's try that.

```haskell
showListInstance :: Universe
showListInstance = $(mkUniverse [d| instance Show a => Show [a] |])
```

Now, let's try combining all three.

```
*Data.ClosedWorld.TH Data.ClosedWorld Data.ClosedWorld.Base Data.ClosedWorld.TH> showMyDynamic (showIntInstance <> showCharInstance <> showListInstance)  myList
[Just "1",Just "\"hello world\"",Nothing,Nothing,Nothing,Nothing,Nothing,Just "[1,2,3,4,5]",Just "[\"hello\",\"world\"]"]
```

Great! We recovered the `Show String` instance for `"hello world"`. But hold on!
Notice that the `Show` instance for `Show [Int]` and `Show [[Char]]` was
recovered as well! Indeed, `Universe`s can hold both explicit instance
dictionaries, as well as *instructions on how to make those dictionaries*.

There's still a few `instance`s we don't have. Let's define `Show (a, b)` and
`Show (Maybe a)`.

```haskell
miscShowInstances :: Universe
miscShowInstances = $(mkUniverse [d|instance (Show a, Show b) => Show (a, b); instance Show a => Show (Maybe a) |])
```

Now, everything can be shown.

```
*Data.ClosedWorld.TH Data.ClosedWorld Data.ClosedWorld.Base Data.ClosedWorld.TH> showMyDynamic (showIntInstance <> showCharInstance <> showListInstance)  myList
[Just "1",Just "\"hello world\"",Nothing,Nothing,Nothing,Nothing,Nothing,Just "[1,2,3,4,5]",Just "[\"hello\",\"world\"]"]
*Data.ClosedWorld.Types Data.ClosedWorld Data.ClosedWorld.Base Data.ClosedWorld.TH Data.ClosedWorld.Types> map fromJust (showMyDynamic (showIntInstance <> showCharInstance <> showListInstance <> miscShowInstances )  myList)
["1","\"hello world\"","(\"hello\",3)","(\"hello\",\"world\")","Nothing","Just 34","Just (\"hello, world\",4)","[1,2,3,4,5]","[\"hello\",\"world\"]"]
```

Okay, one more trick! Let's find `Int`s in containers in `myList`. More
specifically, we want to use the `Foldable f` instance (if any) of our
`MyDynamic` types of form `f Int`, to recover all `Int`s in `myList`. Intuitively we want

```haskell
foldMap (\(MyDynamic x) -> superMagicToListIfFoldable x) myList 
```

Let's write `superMagicToListIfFoldable`! Of course, our magic isn't really that
magical, so we'll have to compromise and parameterize our real function by a `Universe`.

```haskell
import Data.Foldable

superMagicToListIfFoldable :: forall a r. (Typeable a, Typeable r) => Universe -> a -> [r]
superMagicToListIfFoldable u a = withHead1 (Proxy @Foldable) u a [] toList
```

First, let's verify that the empty universe has no idea how to fold over
containers containing `Int`s.

```
*Data.ClosedWorld.TH Data.ClosedWorld Data.ClosedWorld.Base Data.ClosedWorld.TH Data.Typeable Data.Foldable> concatMap (\(MyDynamic x) -> superMagicToListIfFoldable mempty x) myList :: [Int]
[]
```

The `Show` `Universe` we defined also doesn't know what to do.

```
*Data.ClosedWorld.TH Data.ClosedWorld Data.ClosedWorld.Base Data.ClosedWorld.TH Data.Typeable Data.Foldable> concatMap (\(MyDynamic x) -> superMagicToListIfFoldable (showIntInstance <> showCharInstance <> showListInstance) x) myList :: [Int]
[]
```

Now, let's define some `Foldable` instances for our universe.

```haskell
foldableInstances :: Universe
foldableInstances = $(mkUniverse [d| instance Foldable Maybe; instance Foldable []; instance Foldable ((,) a) |])
```

These know what to do!

```
*Data.ClosedWorld.TH Data.ClosedWorld Data.ClosedWorld.Base Data.ClosedWorld.TH Data.Typeable Data.Foldable> concatMap (\(MyDynamic x) -> superMagicToListIfFoldable foldableInstances x) myList :: [Int]
[3,34,1,2,3,4,5]
```

We can also restrict ourselves only to lists.

```haskell
foldableListInstance :: Universe
foldableListInstance = $(mkUniverse [d| instance Foldable [] |])
```

Now, only the `Int`s in a list are returned.

```
*Data.ClosedWorld.TH Data.ClosedWorld Data.ClosedWorld.Base Data.ClosedWorld.TH Data.Typeable Data.Foldable> concatMap (\(MyDynamic x) -> superMagicToListIfFoldable foldableListInstance x) myList :: [Int]
[1,2,3,4,5]
```

Alright, that's it!

## How does this work?

A lot of `unsafeCoerce` to make the constraint solver happy. I think it's mostly
type safe.

## Limitations?

Currently, `mkUniverse` can't deal with instances whose instance heads contain
higher-kinded free variables. For example,

```haskell
$(mkUniverse [d| instance Monad m => Monad (StateT s m) |])
```

will likely not work.

The library can handle them internally, but you need to give explicit kind
annotations and it's really messy. Pull requests welcome if you figure this one
out!

## Is there any theory behind this?

No. This was mostly an exercise in using `unsafeCoerce` without segfaulting.

## Should I use this?

Honestly, I have no idea. I wrote it to see if I could, and it turns out I can.
I'm not even sure this is type-safe, *caveat emptor*.
