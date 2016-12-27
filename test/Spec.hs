import Test.DocTest

main :: IO ()
main = doctest ["src/Bears.hs", "src/Bears/TH.hs"]
