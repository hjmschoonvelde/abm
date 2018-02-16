########################################################################
# February 2018
# Script of the ABM presented in:
# Competition in Media Systems and Voter Knowledge: An Agent-Based Model
# Author: Martijn Schoonvelde
# Email: mschoonvelde@gmail.com
#
# NB: Monte Carlo runs will take a long time to run (for 800 simulations: about 5 hours on a 2,7 GHz Intel Core processor, with 16GB memory)
# Users who want faster performance may want use multiple cores
########################################################################

rm(list=ls(all=TRUE))

########################################################################
# load libraries
# NB: these libraries may need to be installed first 
########################################################################

library(msm)
library(foreign)
library(beepr)
library(TTR)
library(ineq)
library(ggplot2)
library(arrayhelpers)

#start timer
ptm <- proc.time()


#load belief updating and outlet selection functions
update.belief <- function(x,y,z){
    x[x[,2]==1,3] <- x[x[,2]==1,3] + (y - x[x[,2]==1,3])*x[x[,2]==1,4] / (x[x[,2]==1,4] + ((1 - x[x[,2]==1,12])) + 0.01)
    x[x[,2]==1,5] <- x[x[,2]==1,5] + (z - x[x[,2]==1,5])*x[x[,2]==1,6] / (x[x[,2]==1,6] + ((1 - x[x[,2]==1,12])) + 0.01)
    x[x[,2]==1 & x[,4] <= .01,4] <- .01
    x[x[,2]==1 & x[,6] <= .01,6] <- .01
    x[x[,2]==1 & x[,4] > .01,4]  <- x[x[,2]==1 & x[,4] > .01,4]*(1 - x[x[,2]==1 & x[,4] > .01,12]) / (x[x[,2]==1 & x[,4] > .01,4] + (1 - x[x[,2]==1 & x[,4] > .01,12]) + 0.01)
    x[x[,2]==1 & x[,6] > .01,6]  <- x[x[,2]==1 & x[,6] > .01,6]*(1 - x[x[,2]==1 & x[,6] > .01,12]) / (x[x[,2]==1 & x[,6] > .01,6] + (1 - x[x[,2]==1 & x[,6] > .01,12]) + 0.01)
return(x)
}

choose.outlet <- function(x,y,z) {
    choice.matrix <- array(0, dim = c(nrow(x),nrow(y)))
    if (N==1) {x[,8] = 1}
    if (N!=1){ 
         choice.matrix <- Vectorize(function(r)  abs((1-z[r])*y[,2] + z[r]*abs(x[r,9] - y[,5])))(seq(nrow(x)))
         choice.matrix <- Vectorize(function(r)  choice.matrix[,r]/sum(choice.matrix[,r]))(seq(ncol(choice.matrix)))
         x[,8] <- Vectorize(function(r) which.max(rmultinom(1,1,prob = choice.matrix[,r]))) (seq(ncol(choice.matrix)))
     }
    x[,12] <- Vectorize(function(r) y[x[r,8],1])(seq(nrow(x)))
    x[,15] <- Vectorize(function(r) abs(x[r,9] - y[x[r,8],5]))(seq(nrow(x)))
    return(x)
}

#Initiate the Monte Carlo parameters; NB: see Figure 1 in the paper for the set-up of the parameters

R <- 800              		                      #Number of Monte Carlo runs
mc_data <- array(0,dim <- c(R,16))                    #Monte Carlo Data set aggregate

#Initiate the model parameters

V <- 1001			                      #number of voters
T <- 2000 			                      #election periods
kappa <- .005                                         #voter learning parameter
mu <-  .005                                           #media learning parameter
delta <- .005                                         #party learning parameter
P <- 2                                                #incumbent and challenger party

party <- array(0,dim <- c(P,4))                       #PARTY VARIABLES 
# 1 ideology
# 2 ideology t-1
# 3 vote share t
# 4 vote share t-1

voter <- array(0, dim <- c(V,18))                     #VOTER VARIABLES
# 1 interest in news (propensity)
# 2 decision to buy news
# 3 mu Party 1
# 4 sigma^2 Party 1
# 5 mu Party 2
# 6 sigma^2 Party 2
# 7 vote choice
# 8 media choice
# 9 ideology
# 10 utility(t)
# 11 utility(t-1)

mc_data_ind <- array(0, dim <- c(R, nrow(voter), ncol(voter))) #Monte Carlo Data set individual
mc_data_media_ind <- array(0, dim <- c(1,8))

data <- array(0,dim <- c(T,16))                        #DATA

pb <- txtProgressBar(min = 0, max = R, style = 3)

for (r in 1:R){			                       #Start Monte Carlo loop
    Sys.sleep(0.1)
    setTxtProgressBar(pb, r)


N <- c(0, 1, 5, 10)
N <- N[1 + as.integer(runif(1,0,4))]

comp <- round(runif(V,0,1),2)                          #voter type parameter
    
media <- array(0, dim <- c(N,7))                       #media characteristics
# 1 quality at time t
# 2 quality at time (t-1)
# 3 media audience share at time t
# 4 media audience share at time (t-1)
# 5 media ideology
# 6 U(t)
# 7 U(t-1)

media.share  <- array(0, dim <- c(T,N))

                                                       #voter characteristics
voter[1:V,1] <- runif(V)                               #propensity to consume news
voter[1:V,3] <- runif(V)                               #initial mu Party 1
voter[1:V,4] <- 1                                      #initial sigma^2 Party 1
voter[1:V,5] <- runif(V)                               #initial mu Party 2
voter[1:V,6] <- 1                                      #initial sigma^2 Party 2
voter[1:V,9] <- round(runif(V), 2)                     #distribution of ideology
voter[1:V,10:11] <- runif(V*2)                         #initial utility at t and (t-1)
voter[,16] <- comp
voter[,17] <- 0
voter[,18] <- 0

party[1,1:2] <- round(runif(2, 0, median(voter[,9])), 2) 
party[2,1:2] <- round(runif(2, median(voter[,9]),1), 2) 
gov <- 1                                               #set Party 1 to be in government
                                                   
media[1:N,1:4] <- round(runif(N*4), 2)                 #initial news quality and audience share
media[,5] <- round(runif(N),2)                         #media ideology
 

for (t in 1:T) {			               #time Loop
data[t,1] <- t                                         #time Counter

voter[,2] <- rbinom(V,1,voter[,1])
x <- rtnorm(1, party[1,1],1,0,1)
y <- rtnorm(1, party[2,1],1,0,1)
w <- party[1,1]
z <- party[2,1]
p <- 0
ifelse(gov == 1, p <- x, p <- y)

                                                       #voter identifies nearest remaining media outlet
#voter[,15] <- Vectorize(function(r) min(abs(voter[r,9] - na.omit(media[,5]))))(seq(nrow(voter)))

                                                       #voters consume news based on propensity to do so and choose outlet
ifelse(N!=0, voter <- choose.outlet(voter, media, comp), voter[,2] <- 0)
voter[voter[,2]==0,8] <- 0
voter <- update.belief(voter, w, z)

if (gov==1) {                                          #news-ignoring voters only learn about incumbent through policy outcomes
  voter[voter[,2]==0,3] <- voter[voter[,2]==0,3] + (x - voter[voter[,2]==0,3])*(voter[voter[,2]==0,4] / (voter[voter[,2]==0,4] + 2))
  voter[voter[,2]==0,4] <- voter[voter[,2]==0,4]*2 / (voter[voter[,2]==0,4] + 2)
}

if (gov==2) {
voter[voter[,2]==0,5] <- voter[voter[,2]==0,5] + (y - voter[voter[,2]==0,5])*(voter[voter[,2]==0,6] / (voter[voter[,2]==0,6] + 2))
voter[voter[,2]==0,6] <- voter[voter[,2]==0,6]*2 / (voter[voter[,2]==0,6] + 2)
}
                                                       
voter[,13] <- rnorm(V,voter[,3],voter[,4])             #voters vote sincerely based on the information they have
voter[,14] <- rnorm(V,voter[,5],voter[,6])

voter[,13] <- abs(voter[,13] - voter[,9])
voter[,14] <- abs(voter[,14] - voter[,9])

voter[voter[,13] <= voter[,14],7] <- 1
voter[voter[,13] > voter[,14],7] <- 2

voter[,18] <- 0
voter[voter[,7] == 1 & abs(voter[,9] - party[1,1]) > abs(voter[,9] - party[2,1]), 18] <- 1
voter[voter[,7] == 2 & abs(voter[,9] - party[2,1]) > abs(voter[,9] - party[1,1]), 18] <- 1

                                                       #voters obtain utility and update interest in news
voter[voter[,2]==0,10] <-  - abs(voter[voter[,2]==0,9] - p)
voter[voter[,2]==1,10] <-  - abs(voter[voter[,2]==1,9] - p) - abs((1-voter[voter[,2]==1,16])*voter[voter[,2]==1,12] + voter[voter[,2]==1,16]*voter[voter[,2]==1,15])
voter[voter[,2]==0 & voter[,10] <= voter[,11],1] <-  voter[voter[,2]==0 & voter[,10] <= voter[,11],1] + kappa
voter[voter[,2]==0 & voter[,10] > voter[,11],1]  <-  voter[voter[,2]==0 & voter[,10] > voter[,11],1] - kappa
voter[voter[,2]==1 & voter[,10] > voter[,11],1]  <-  voter[voter[,2]==1 & voter[,10] > voter[,11],1] + kappa
voter[voter[,2]==1 & voter[,10] <= voter[,11],1] <-  voter[voter[,2]==1 & voter[,10] <= voter[,11],1] - kappa
voter[voter[,1] > 0.99,1] <- 0.99
voter[voter[,1] < 0.01,1] <- 0.01
voter[voter[,2]==1,17] <- voter[voter[,2]==1,17] + 1
voter[,] <- round(voter[,], 3)

                                                        #votes are counted and party with most votes wins election
party[1,3] <- sum(voter[1:V,7]==1)/V
party[2,3] <- sum(voter[1:V,7]==2)/V
gov <- which.max(party[,3])
                                                      
media[,3] <- Vectorize(function(r) sum((voter[1:V,8]==r)))(seq(nrow(media)))
media[,6] <- round((media[,3]/V) - media[,2],2)

for (n in 1:N) {                                        #media update quality of reporting using sampling of preferences
if (sum(voter[,8]==n) == 0) {break}
sample.readers <- mean(sample(voter[voter[,8]==n, 1], 20, replace = TRUE))
ifelse(sample.readers >= media[n,2], media[n,1] <- media[n,2] + mu, media[n,1] <- media[n,2] - mu)
if(media[n,1] > media[n,6]) {media[n,1] <- media[n,6]}
if(media[n,1] < 0.01) {media[n,1] = 0.01}
}
                                                        #losing candidates update platform using sampling of beliefs
sample.voters <- median(sample(voter[,9], 20, replace = TRUE))
ifelse(party[-gov,1] < sample.voters, party[-gov,1] <- party[-gov,2] + delta, party[-gov,1] <- party[-gov,2] - delta)

data[t,2] <- gov                                        #government party
data[t,3] <- party[1,1]                                 #ideology party 1
data[t,4] <- party[2,1]                                 #ideology party 2
data[t,5] <- party[gov,3]                               #government vote share
data[t,6] <- NA
data[t,7] <- round(sum(voter[,2]==1)/V,2)               #share of informed voters
data[t,8] <- NA                                                     
data[t,9] <- 0.5*(abs(median(voter[,9]) - party[1,1]) + abs(median(voter[,9]) - party[2,1]))

alt <- array(0,dim=c(T,2))                              #calculate no of alternations
alt[,1]= data[,2]
for (i in 2:T) {
if (alt[i,1]!=alt[i-1,1]) alt[i,2]=1
}

data[t,10] <- sum(alt[1:t,2])                           #number of alternations

data[t,11] <- 1 - mean(abs(voter[,3] - party[1,2]))     #avg knowledge party 1
data[t,12] <- 1 - mean(abs(voter[,5] - party[2,2]))     #avg knowledge party 2
data[t,13] <- 1 - 0.5*(mean(abs(voter[,3] - party[1,2])) + mean(abs(voter[,5] - party[2,2])))
data[t,14] <- ifelse(data[t,9] < 0.01, 1, 0)
data[t,15] <- conc(media[,3], type = "Herfindahl")
data[t,16] <- sum(voter[,18])/V

voter[1:V,11] <- voter[1:V,10]                          #voters update and reset utility

if(N!=0) {media[1:N,2] <- media[1:N,1]}
if(N!=0) {media[1:N,4] <- media[1:N,3]}
if(N!=0) {media[1:N,7] <- media[1:N,6]}
            
              
party[1:P,4] <- party[1:P,3]                            #parties reset vote shares and ideology
party[1:P,2] <- party[1:P,1]
a = x = y = w = z = p = 0
}					                #Close Time Loop
data[,]   <- round(data[,], 3)

mc_data[r,1] <-  N                                        #number of outlets                                
mc_data[r,2] <-  mean(data[((3*T/4)+1):T,7])              #average share of informed voters 
mc_data[r,3] <-  sum(data[((3*T/4)+1):T,2] == 1)          #number of times party 1 was in office              
mc_data[r,4] <-  mean(data[((3*T/4)+1):T,3])              #mean ideology party 1
mc_data[r,5] <-  mean(data[((3*T/4)+1):T,4])              #mean ideology party 2
mc_data[r,6] <-  mean(abs(data[((3*T/4)+1):T,3] - median(voter[,9])))    #mean ideological distance party 1 from median voter
mc_data[r,7] <-  mean(abs(data[((3*T/4)+1):T,4] - median(voter[,9])))    #mean ideological distance party 2 from median voter                                    
mc_data[r,8] <-  median(voter[,9])                        #median voter
mc_data[r,9] <-  sum(data[((3*T/4)+1):T,14])              #over time representativeness
mc_data[r,10] <- mean(data[((3*T/4)+1):T,11])             #average knowledge party 1
mc_data[r,11] <- mean(data[((3*T/4)+1):T,9])              #average party distance
mc_data[r,12] <- data[T,10] - data[((3*T/4)+1),10]        #total number of alternations in power
mc_data[r,13] <- mean(data[((3*T/4)+1):T,15], na.rm = TRUE) #average Herfindahl
mc_data[r,14] <- mean(data[((3*T/4)+1):T,12])             #average knowledge party 2
mc_data[r,15] <- which.max(data[,14])                     #initial representativeness
mc_data[r,16] <- mean(data[((3*T/4)+1):T,16])

party[,] = 0
voter[,] = 0
media[,] = 0
data[,]  = 0
}	                                                  #Close Monte Carlo Loop				                 

mc_data[,] <- round(mc_data[,], 3)
mc_data <- as.data.frame(mc_data)
mc_data_ind <- array2df(mc_data_ind)
names(mc_data_ind) <- c("Outcome", "MC.Run", "Voter", "Variable")
names(mc_data) <- c("N","Avg.Share.Inf", "Party.1.Office","PID1","PID2","Dist1","Dist2","MV","Over.Time.Rep","AvgKnow1","Avg.Party.Dist","Alternations", "Herfindahl", "AvgKnow2", "Initial.Rep", "Wrong.Vote")

save(mc_data, file = "ModelOutput.Rdata")
save(mc_data_ind, file = "ModelOutputInd.Rdata")
save(mc_data_media_ind, file = "ModelOutputMediaInd.Rdata")

close(pb)
proc.time() - ptm;
beep()

