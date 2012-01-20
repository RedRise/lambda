\name{lambda}
\alias{lambda}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
Calls a function on a bunch of subparts of a data-structure
}
\description{
Apply a fun on subpart of a [list of [list of...]] arrays according
to a set of iterators. This function can be seen as an extension of
apply.
}
\usage{
lambda(fun, M, ds = if (is.list(M)) {
    1
} else {
    if (is.matrix(M)) 
        2
    else NULL
}, ..., struct = TRUE, simp = TRUE)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{fun}{
The function to be applied.
}
  \item{M}{
The data-structure (array, or list (of list...) of arrays to iterate over.
}
  \item{ds}{
a vector of interger (like MARGIN in apply), or a list of iterators.
}
  \item{\dots}{
optional arguments to fun.
}
  \item{struct}{
boolean (default=TRUE). If FALSE, the intermediate exctracted data will be rendered as vector.
If TRUE the original structure will be preserved.

}
  \item{simp}{
boolean (default=TRUE). If FALSE results will not be put into a more convenient form.
}
}
\details{
%%  ~~ If necessary, more details than the description above ~~
}
\value{
Returns a data-structure built from each FUN call result. If simp=TRUE,
tries to re-arrange it into an array..
}
\references{
%% ~put references to the literature/web site here ~
}
\author{
EONOS INVESTMENT TECHNOLOGIES
}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
Different available iterators: \code{\link{dx}},\code{\link{Idx}},\code{\link{win}},\code{\link{ap}}
}
\examples{

## Generate a simple matrix with dimnames
x <- matrix( rnorm(20), 5, 4 )
rownames(x) <- paste('row',1:nrow(x),sep='_')
colnames(x) <- paste('col',1:ncol(x),sep='_')

## colSums like
lambda( sum, x, 2 )

## rolling-windows sums
lambda( sum, x, win(2) )

}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{ ~kwd1 }
\keyword{ ~kwd2 }% __ONLY ONE__ keyword per line
