module Lib

record Votes where
       constructor MkVotes
       upvotes : Integer
       downvotes : Integer

record Article where
       constructor MkArticle
       title : String
       url : String
       score : Votes

getScore : Article -> Integer
getScore ar = let s = score ar in upvotes s - downvotes s

addUpvote : Article -> Article
addUpvote = { score->upvotes $= (+1) }

addDownvote : Article -> Article
addDownvote = { score->downvotes $= (+1) }

badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)
