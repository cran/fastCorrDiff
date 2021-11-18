\name{SS}
\alias{SS}
\title{
Spectral screening of a differential correlation matrix
}
\description{
The full matrix version of spectral screening method.
}
\usage{
SS(D, K, K.seq = FALSE, sv = FALSE)
}
\arguments{
  \item{D}{
The difference matrix of two correlation/covariance matrices
}
  \item{K}{
The rank K or the maximum rank K to calculate the spectral scores
}
  \item{K.seq}{
logical value. If TRUE, then it returns the spectral screening scores for all rank from 1 to K. If FALSE (default), it returns the rank K result
}
  \item{sv}{
logical value. If TRUE, the square roots of singular values will be used in the score calculation. 
}
}
\details{
This is the full version spectral screening method, which can be applicable to a few thousands of variables. If a tuning of K is needed, please use the fast.SS for tuning.
}
\value{
%%  ~Describe the value returned
%%  If it is a LIST, use
  \item{R}{The the singular vector matrix. Each row is for one variable.}
  \item{R.sv }{The R matrix scaled by sqrt of singular values}
  \item{score}{The spectral score for screening}
%% ...
}
\references{
Tianxi Li, Xiwei Tang, and Ajay Chatrath. Compressed spectral screening for large-scale differential correlation analysis with application in selecting Glioblastoma gene modules. arXiv preprint arXiv:2111.03721, 2021.
}
\author{
Tianxi Li and Xiwei Tang
Maintainer: Tianxi Li  \email{tianxili@virginia.edu}
}
\seealso{
\code{\link{fast.SS}}
}
\examples{

X1 <- matrix(rnorm(200),10,20)
C1 <- cor(X1)
X2 <- matrix(rnorm(200),10,20)
C2 <- cor(X2)

D <- C1-C2

fit <- SS(D, 3, K.seq = FALSE, sv = FALSE)

fit$score

}
