#!/usr/bin/env python
# coding: utf-8

# In[91]:


import random
import socket
import struct
import numpy as np
import copy
import hashlib
import matplotlib.pylab as plt
import intervals

from pprint import pprint
import pandas as pd
import sys
from scipy.stats.kde import gaussian_kde
import scipy.stats as stats
from numpy import linspace
import math


# In[92]:


#Defining Parameters
numberOfBitsOfHash = 160 #As SHA-1
# numberOfBitsOfHash=4
numberOfNodes=1000
numberOfDataPoints=10000
numberOfSearchQueries=1000000
addHops={}
nodeListDictionary={}
masterNode={}
if len(sys.argv)>1:
    if sys.argv[1]=="--log-enable":
        logEnabled=1
    elif sys.argv[1]=="--help":
        print("To execute Code : python ChordFinal.py")
        print("To enable logs: python ChordFinal.py --log-enable")
        exit(0)
    else:
        print("Invalid Option")
        exit(0)
else:
    logEnabled=0

path=""


# In[93]:


#Generic Functions
def contains(key1,lowerBound,upperBound,numberOfBitsOfHash,flag):
    if lowerBound==upperBound and flag==2 and key1==lowerBound:
        return 0
    elif lowerBound==upperBound:
        return 1
    if(flag==1): #Closed Interval
        if key1==lowerBound or key1==upperBound:
            return 1
    elif(flag==2): #Open Interval
        if key1==lowerBound or key1==upperBound:
            return 0
    elif(flag==3): #open closed interval
        if key1==lowerBound:
            return 0
        elif key1==upperBound:
            return 1
    elif(flag==4): #closed open interval
        if key1==lowerBound:
            return 1
        elif key1==upperBound:
            return 0


    if lowerBound<upperBound:
        diff = upperBound - lowerBound
        temp1 = key1 - lowerBound
        temp2 = upperBound-key1
        if temp1<diff and temp2<diff:
            return 1
        else:
            return 0
    elif lowerBound>upperBound:
        temp=lowerBound
        lowerBound=upperBound
        upperBound=temp
        diff = upperBound - lowerBound
        temp1 = key1 - lowerBound
        temp2 = upperBound-key1
        if temp1<diff and temp2<diff:
            return 0
        else:
            return 1

def initializeFingerTableOfFirstNode(firstNode):
    start_list=[]
    interval_list=[]
    successorList=[]
    for k in range(1,numberOfBitsOfHash+1):
        start=(firstNode.nodeId+pow(2,k-1))%(pow(2,numberOfBitsOfHash))
        end=(firstNode.nodeId+pow(2,k)-1)%(pow(2,numberOfBitsOfHash))
        start_list.append(start)
        successorList.append(firstNode)
    fingerTable = np.rec.fromarrays((start_list,successorList ), names=('start','node'))

    return fingerTable

def createChordRing(firstNode):
    firstNode.successor=firstNode
    firstNode.fingerTable=initializeFingerTableOfFirstNode(firstNode)
    firstNode.predecessor = firstNode
    return firstNode


def initializeNewNode(newNodeId):
    newNode = Node(newNodeId)
    newNode.successor = masterNode.findSuccessor(newNode.nodeId)
#     newNode.successor = firstNode.findSuccessor(newNode.nodeId)
    newNode.fingerTable = initializeFingerTableOfFirstNode(newNode)
    return newNode

def printFingerTable(node):
    start=[]
    nodelist=[]
    for i in node.fingerTable:
        start.append(i[0])
        nodelist.append(i[1].nodeId)
    df = pd.DataFrame({"Start":start,"Node":nodelist})
    print(df.to_string(index=False))

def printAllNodes():
    nodeListDictionary1={}
    nodeListDictionary1={masterNode.nodeId:nodeListDictionary[masterNode.nodeId]}
    for i in sorted(list(nodeListDictionary1.keys())):
        print(" Node - ",i)
        print(" Successor - ",nodeListDictionary1[i].successor.nodeId)
        print(" Predecessor - ",nodeListDictionary1[i].predecessor.nodeId)
        printFingerTable(nodeListDictionary1[i])
        print("--------------------------------")


def addFirstTwoNodes(firstNode,secondNode):
    for index,i in enumerate(firstNode.fingerTable):
        if contains(i.start,firstNode.nodeId,secondNode.nodeId,numberOfBitsOfHash,1):
            firstNode.fingerTable[index].node=secondNode

    for index,i in enumerate(secondNode.fingerTable):
        if contains(i.start,secondNode.nodeId,firstNode.nodeId,numberOfBitsOfHash,1):
            secondNode.fingerTable[index].node=firstNode

    firstNode.successor=secondNode
    firstNode.predecessor=secondNode
    secondNode.successor=firstNode
    secondNode.predecessor=firstNode
    return (firstNode,secondNode)



#Storing 10000 dataPoints
def storingDataPoints():
    dataStoredTemp=random.sample(range(10, 1000000), 10000)
    for index,i in enumerate(dataStoredTemp):
        data = str(i)
        keyData = int(hashlib.sha1(data.encode('utf-8')).hexdigest(),16)
        masterNode.addData(keyData,data)
    return dataStoredTemp


# In[94]:


class Node:
    def __init__(self, nodeId):
        self.nodeId = nodeId
        self.fingerTable = None
        self.predecessor=None
#         self.successor=[nodeId]
        self.successor=None
        self.data={}

    #Find Successor
    def findClosestPreceedingFinger(self,id):
        for i in range(numberOfBitsOfHash-1,-1,-1):
            if(contains(self.fingerTable[i].node.nodeId,self.nodeId,id,numberOfBitsOfHash,2)):
                return self.fingerTable[i].node
        return self

    def findPredecessor(self,id):
        idCopy=self
        jumps=0
        global path
        while (not contains(id,idCopy.nodeId,idCopy.successor.nodeId,numberOfBitsOfHash,3)):
            path+=str(idCopy.nodeId)+"->"
            jumps+=1
            idCopy=idCopy.findClosestPreceedingFinger(id)
        global addHops
        addHops[id]=jumps
        return idCopy

    def findSuccessor(self,id):
        predecessor = self.findPredecessor(id)
        return predecessor.successor

    #Joining a node
    def updateFingerTable(self,node,i):
        if contains(node.nodeId,self.nodeId,self.fingerTable[i].node.nodeId,numberOfBitsOfHash,4):
            self.fingerTable[i].node = node
            p = self.predecessor
            if p.nodeId!=node.nodeId:
                p.updateFingerTable(node,i)

    def updateOthers(self):
        for i in range(1,numberOfBitsOfHash+1):
            pred = self.findSuccessor((self.nodeId - pow(2,i-1))%pow(2,numberOfBitsOfHash))
            if not pred.nodeId==(self.nodeId - pow(2,i-1))%pow(2,numberOfBitsOfHash):
                pred = self.findPredecessor((self.nodeId - pow(2,i-1))%pow(2,numberOfBitsOfHash))
            if pred.nodeId==self.nodeId:
                continue
            pred.updateFingerTable(self,i-1)

    def initFingerTable(self,existingNode):
        self.fingerTable[0].node = existingNode.findSuccessor(self.fingerTable[0].start)
        self.successor = self.fingerTable[0].node
        self.predecessor = self.successor.predecessor
        self.successor.predecessor = self
        self.predecessor.successor = self
        self.predecessor.fingerTable[0].node = self
        for i in range(0,numberOfBitsOfHash-1):
            if contains(self.fingerTable[i+1].start,self.nodeId,self.fingerTable[i].node.nodeId,numberOfBitsOfHash,4):
                self.fingerTable[i+1].node = self.fingerTable[i].node
            else:
                self.fingerTable[i+1].node = existingNode.findSuccessor(self.fingerTable[i+1].start)

    def transferKeys(self,successor):
        updated_keys = []
        for key,value in successor.data.items():
            if int(key)<=int(self.nodeId):
                self.data[key]=value
                updated_keys.append(key)
            else:
                continue
        for i in updated_keys:
            del successor.data[i]

    def join(self,existingNode):
        self.initFingerTable(existingNode)
        self.updateOthers()
        self.transferKeys(self.successor)


    #Node Failure
    def updateFingerTableOnFailure(self,node,i):
        if(node.nodeId==self.fingerTable[i].node.nodeId):
            self.fingerTable[i].node=node.successor
            p = self.predecessor
            p.updateFingerTableOnFailure(node,i)

    def updateOthersOnFailure(self):
        for i in range(1,numberOfBitsOfHash+1):
            pred = self.findSuccessor((self.nodeId - pow(2,i-1))%pow(2,numberOfBitsOfHash))
            if not pred.nodeId==(self.nodeId - pow(2,i-1))%pow(2,numberOfBitsOfHash):
                pred = self.findPredecessor((self.nodeId - pow(2,i-1))%pow(2,numberOfBitsOfHash))
            pred.updateFingerTableOnFailure(self,i-1)

    def transferDataToSuccessor(self):
        succ = self.successor
        succ.data.update(self.data)

    def nodeFailure(self):
        self.transferDataToSuccessor()
        self.updateOthersOnFailure()
        self.predecessor.successor=self.successor
        self.successor.predecessor=self.predecessor


    #Stabilization of Network
    def notify(self,origNode):
        if self.predecessor or contains(origNode.nodeId,self.predecessor.nodeId,self.nodeId,numberOfBitsOfHash,2):
            self.predecessor=origNode

    def stabilize(self):
        x = self.successor.predecessor
        if contains(x.nodeId,self.nodeId,self.successor.nodeId,numberOfBitsOfHash,2):
            self.successor=x
        self.successor.notify(self)

    def fixFingerTables(self):
        for i in range(0,numberOfBitsOfHash):
            self.fingerTable[i].node = self.findSuccessor(self.fingerTable[i].start)
        return self

    #Adding data to a node
    def addData(self,key,value):
        nodeOfData = self.findSuccessor(key)
        if key not in nodeOfData.data.keys():
            nodeOfData.data[key]=[]
            nodeOfData.data[key].append(value)
        else:
            nodeOfData.data[key].append(value)

    #Lookup Query
    def lookup(self,key):
        requiredNode = self.findSuccessor(key)
        if key in requiredNode.data.keys():
            return requiredNode
        return None



# In[96]:

print("here")
fp = open("logFile.log","w")
totalData={}
totalDataAfterDeletion={}
numNodes = [100,500,1000]
back1 = {}
for numnodes in numNodes:
    back1 = nodeListDictionary
    nodeListDictionary={}
    #Generate IP Addresses
    print("------------------Number of Nodes : ",numnodes,"---------------------")
    numberOfNodes=numnodes
    totalData[numnodes]=[]
    print("--------------Generating IP Addresses-------------------")
    all_ip_address=[]
    dataStored=[]
    for i in range(0,numberOfNodes):
        temp = socket.inet_ntoa(struct.pack('>I', random.randint(0x3cffffff, 0xffffffff)))
        if(temp not in all_ip_address):
            all_ip_address.append(temp)
        else:
            i-=1

    print("-------------Calculating SHA-1 hash of all IP Addresses-----------------")
    #Calculating SHA-1 (160 bit) hash of IP Address of a node
    hashSet = {}
    for ip in all_ip_address:
        hashSet[ip]=int(hashlib.sha1(ip.encode('utf-8')).hexdigest(),16)

    sortedHashSet = {k: v for k, v in sorted(hashSet.items(), key=lambda item: item[1])}
    sortedKeys = list(sortedHashSet.keys())

    masterNode = Node(sortedHashSet[sortedKeys[0]])
    masterNode = createChordRing(masterNode)
    secondNode=initializeNewNode(sortedHashSet[sortedKeys[1]])
    (masterNode,secondNode)=addFirstTwoNodes(masterNode,secondNode)
    nodeListDictionary={}
    nodeListDictionary[sortedHashSet[sortedKeys[0]]]=masterNode
    nodeListDictionary[sortedHashSet[sortedKeys[1]]]=secondNode

    print("----------------Adding Nodes to the Chord Network----------------")
    for i in range(2,numberOfNodes):
        print(i)
        path=""
        tempNode = initializeNewNode(sortedHashSet[sortedKeys[i]])
        tempNode.join(masterNode)
        fp.write(str(tempNode.nodeId)+" Path:" +path+"\n")
        nodeListDictionary[sortedHashSet[sortedKeys[i]]]=tempNode

    #Fixing Finger Tables
    for key,value in nodeListDictionary.items():
        nodeListDictionary[key]=value.fixFingerTables()

    #Storing Data
    print("-----------------Storing Data-----------------------------")
    dataStored=storingDataPoints()

    dataToSearch = random.sample(range(1, 1060000), numberOfSearchQueries)

    print("-----------------Search Begins----------------------------")

    hopData = {}
    flag = 0
    for i in dataToSearch:
#         print("Required Data ",i)
        if flag%1000==0:
            print("Data Searched: ",flag)
        hashValueOfData = int(hashlib.sha1(str(i).encode('utf-8')).hexdigest(),16)
        addHops[hashValueOfData]=0
        result = masterNode.lookup(hashValueOfData)
        hopData[hashValueOfData]=addHops[hashValueOfData]
        flag+=1

    totalData[numnodes].append(hopData)
    print("-----------Deleting 50% nodes------------------")
    allKeys = list(nodeListDictionary.keys())
    allKeys.remove(masterNode.nodeId)
    toBeDeleted = random.sample(allKeys,int(numnodes/2))
    for i in toBeDeleted:
        nodeListDictionary[i].nodeFailure()

    hopData = {}
    flag = 0
    print("-----------Searching Again------------------")
    for i in dataToSearch:
#         print("Required Data ",i)
        if flag%1000==0:
            print("Data Searched: ",flag)
        hashValueOfData = int(hashlib.sha1(str(i).encode('utf-8')).hexdigest(),16)
        addHops[hashValueOfData]=0
        result = masterNode.lookup(hashValueOfData)
        hopData[hashValueOfData]=addHops[hashValueOfData]
        flag+=1
    totalDataAfterDeletion[numnodes] = []
    totalDataAfterDeletion[numnodes].append(hopData)

fp.close()


#----------------PLOTS-------------------
print("------------plots before deletion--------------")
mapAverageHopsMean = {}
mapAverageHopsStd = {}
mapAverageHops = {}
for key,value in totalData.items():

    mapAverageHops[key]=0
    count=0
    for i,j in value[0].items():
        count+=j
    listofvalues = [j for i,j in value[0].items()]
    mapAverageHopsMean[key]=np.mean(listofvalues)
    mapAverageHopsStd[key]=np.std(listofvalues)

lists = sorted(mapAverageHopsMean.items())
lists1 = sorted(mapAverageHopsStd.items())
x, y = zip(*lists)
a,b = zip(*lists1)
fig1 = plt.figure()
plt.errorbar(x, y, b, linestyle='None', marker='^')
plt.xlabel("Number Of Nodes")
plt.ylabel("Path Length")
# plt.show()
plt.title("Path Length vs Number Of Nodes originally ")
plt.savefig("nodesPathLength.eps",format="eps")

numnodes = [100,500,1000]
for i in numnodes:
    fig1 = plt.figure()
    test = totalData[i][0]
    new = {}
    for k,v in test.items():
        if v not in new.keys():
            new[v]=[]
        new[v].append(k)

    new_data = {k:len(v)/numberOfSearchQueries for k,v in new.items()}
    import matplotlib.pylab as plt
    plt.figure(figsize=(15,5))
    plt.bar(new_data.keys(), new_data.values(), width=.5, color='g')
    plt.xlabel("Path Length")
    plt.ylabel("Probability")
    plt.title("Path Length vs Probability for N="+str(i))
    plt.savefig("pathLengthProbability_"+str(i)+".eps",format="eps")

for i in numnodes:
    out = []
    fig1 = plt.figure()
    for k,v in totalData[i][0].items():
        out.append(v)
    kde = gaussian_kde( out )
    mu = np.mean(out)
    variance = np.var(out)
    sigma = math.sqrt(variance)
    dist_space = np.linspace(mu - 3*sigma, mu + 3*sigma, 100)
    plt.plot(dist_space, stats.norm.pdf(dist_space, mu, sigma))
    plt.xlabel("Path Length")
    plt.ylabel("PDF")
    plt.title("Path Length PDF")
    plt.savefig("pathLengthpdf_"+str(i)+".eps",format="eps")

print("--------------plots after deletion---------------")
mapAverageHopsMean = {}
mapAverageHopsStd = {}
mapAverageHops = {}
for key,value in totalDataAfterDeletion.items():

    mapAverageHops[key]=0
    count=0
    for i,j in value[0].items():
        count+=j
    listofvalues = [j for i,j in value[0].items()]
    mapAverageHopsMean[key]=np.mean(listofvalues)
    mapAverageHopsStd[key]=np.std(listofvalues)

lists = sorted(mapAverageHopsMean.items())
lists1 = sorted(mapAverageHopsStd.items())
x, y = zip(*lists)
a,b = zip(*lists1)
fig1 = plt.figure()
plt.errorbar(x, y, b, linestyle='None', marker='^')
plt.xlabel("Number Of Nodes")
plt.ylabel("Path Length")
# plt.show()
plt.title("Path Length vs Number Of Nodes on 50% deletion")
plt.savefig("nodesPathLengthDel.eps",format="eps")

numnodes = [100,500,1000]
for i in numnodes:
    fig1 = plt.figure()
    test = totalDataAfterDeletion[i][0]
    new = {}
    for k,v in test.items():
        if v not in new.keys():
            new[v]=[]
        new[v].append(k)

    new_data = {k:len(v)/numberOfSearchQueries for k,v in new.items()}
    import matplotlib.pylab as plt
    plt.figure(figsize=(15,5))
    plt.bar(new_data.keys(), new_data.values(), width=.5, color='g')
    plt.xlabel("Path Length")
    plt.ylabel("Probability")
    plt.title("Path Length vs Probability for N="+str(i//2))
    plt.savefig("pathLengthProbabilityDel_"+str(i//2)+".eps",format="eps")

for i in numnodes:
    fig1 = plt.figure()
    out = []
    for k,v in totalDataAfterDeletion[i][0].items():
        out.append(v)
    kde = gaussian_kde( out )
    mu = np.mean(out)
    variance = np.var(out)
    sigma = math.sqrt(variance)
    dist_space = np.linspace(mu - 3*sigma, mu + 3*sigma, 100)
    plt.plot(dist_space, stats.norm.pdf(dist_space, mu, sigma))
    plt.xlabel("Path Length")
    plt.ylabel("PDF")
    plt.title("Path Length PDF for N="+str(i//2))
    plt.savefig("pathLengthpdfdel_"+str(i//2)+".eps",format="eps")
