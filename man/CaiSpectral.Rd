\name{CaiSpectral}
\alias{CaiSpectral}
\title{
Spectral project algorithm of Cai et al (2017).
}
\description{
Spectral projection algorithm of Cai et al (2017), which is based on the rank 1 spectral structure.
}
\usage{
CaiSpectral(D)
}
\arguments{
  \item{D}{
The differential correlation matrix
}
}
\details{
See the reference
}
\value{
The spectral scores. It is recommened in the paper to use any two-class clustering algorithm to separate the variables.
}
\references{
T. T. Cai, T. Liang, A. Rakhlin, et al. Computational and statistical boundaries for submatrix localization
in a large noisy matrix. The Annals of Statistics, 45(4):1403-1430, 2017.
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

fit <- CaiSpectral(D)

fit

}
