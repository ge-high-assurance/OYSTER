import random
from lxml import etree as ET
import lxml.etree

###Global Variabl declaration####
Num_End_Device = 6
Num_Bridges = 2
TotalNumStreams = 0
ListOfStreams = []
ListOfIDs = []
ListOfFramesPerPeriod = []
ListOfMaxFrameSize = []
ListOfRefreshPeriod = []
ListOfIpAddress = []

################Stream file reading and parsing###########
with open("Stream_Level_ICD_V1.xml", "r") as f:
	stream = f.read()
stream= ET.parse('Stream_Level_ICD_V1.xml')
root = stream.getroot()

################Generate IP Adresses######################

for l in range (Num_End_Device*2):
    ListOfIpAddress.append("10.1.1."+str(l+2))
print (ListOfIpAddress)

	########################Total Number of Streams###################
for elem in stream.iter():
    if (elem.tag=="Stream"):
        TotalNumStreams=TotalNumStreams+1
        
	#################Collecting the important stream parameters ################
for j in range (5): 
    ListOfTemp=[]
    for elem in stream.iter():
            if (elem.tag=="Stream"):
                
                my_list=str(elem.attrib).split(',')
                myStreamname= my_list[j].split(':')
                myStreamname.remove(myStreamname[0])
                strg=myStreamname[0]
                new_string = strg.replace("'", '')
                if (j==4):
                    new_string=new_string.replace("}", "")
                ListOfTemp.append(new_string)
		
    if j==0:
        ListOfStreams=ListOfTemp
    elif j==1:
        ListOfIDs=ListOfTemp
    elif j==2:
        ListOfFramesPerPeriod=ListOfTemp
    elif j==3:
        ListOfMaxFrameSize=ListOfTemp
    elif j==4:
        ListOfRefreshPeriod=ListOfTemp

print ("The total number of Stream is=", TotalNumStreams)
print ("The total List of Stream is=", ListOfStreams)
print ("The total List of List Of Frames Per Period is=", ListOfFramesPerPeriod)
print ("The total List of ListOfMaxFrameSize is=", ListOfMaxFrameSize)
print ("The total List of ListOfRefreshPeriod is=", ListOfRefreshPeriod)

############################## Generating QCC file ########################
def GeneratQcc(Qcc):
	Root_Qcc= ET.Element("qcc-inputs")
	Root_Qcc.set("xmlns", "urn:ieee:std:802.1Q:yang:ge-qcc")
	
	for i in range (len(ListOfStreams)):
		stream = ET.SubElement(Root_Qcc, "stream-configuration")
		streamID=ET.SubElement(stream, "stream-id")
		streamID.text=(ListOfStreams[i])#"00-0a-35-00-01-10:17-7c")
		talker=ET.SubElement(stream, "talker")
		StreamRank=ET.SubElement(talker, "stream-rank" )
		Rank=ET.SubElement(StreamRank, "rank")
		Rank.text=("0")
		endStainter=ET.SubElement(talker, "end-station-interfaces")# ("end"+"-"+"station"+"-"+"interfaces"))
		Mac=ET.SubElement(endStainter, "mac-address")
		Mac.text=("00-0a-35-00-01-10")
		intName=ET.SubElement(endStainter, "interface-name")
		DF=ET.SubElement(talker, "data-frame-specification")
		Index= ET.SubElement(DF, "index")
		Index.text=("1")
		IpTup= ET.SubElement(DF, "ipv4-tuple")
		SrcIP= ET.SubElement (IpTup, "source-ip-address")
		SrcIP.text=(ListOfIpAddress[i])#("10.1.1.11")
		DstIP= ET.SubElement (IpTup, "destination-ip-address")
		DstIP.text=(ListOfIpAddress[i+1])#("10.1.1.12")
		Dscp = ET.SubElement (IpTup, "dscp")
		Dscp.text=("0")
		Protocol = ET.SubElement (IpTup, "protocol")
		Protocol.text=("17")
		SrcPort =ET.SubElement (IpTup, "source-port")
		SrcPort.text=("0")
		DstPort =ET.SubElement (IpTup,"destination-port")
		DstPort.text=("6012")
		TrafSpec=ET.SubElement (talker, "traffic-specification")
		Interval= ET.SubElement (TrafSpec, "interval")
		Numerator= ET.SubElement (Interval, "numerator")
		Numerator.text=("1")
		Denominator=ET.SubElement (Interval, "denominator")
		Denominator.text=("1000")
		MFPintrval=ET.SubElement (TrafSpec, "max-frames-per-interval")
		MFPintrval.text=ListOfFramesPerPeriod[i] #("1")
		MFSiz=ET.SubElement (TrafSpec, "max-frame-size")
		MFSiz.text = (ListOfMaxFrameSize[i]) #("1044")
		TSelcttion=ET.SubElement(TrafSpec,"transmission-selection")
		TSelcttion.text = ("0")
		TimeAware=ET.SubElement(TrafSpec, "time-aware")
		EarliestTranOffset=ET.SubElement(TimeAware, "earliest-transmit-offset")
		EarliestTranOffset.text=("0")
		LatestTransOffset=ET.SubElement(TimeAware, "latest-transmit-offset")
		LatestTransOffset.text=("0")
		Jitter=ET.SubElement(TimeAware, "jitter")
		Jitter.text=("0")
		UserToNtkReq=ET.SubElement(talker, "user-to-network-requirements")	
		NumSemTrees=ET.SubElement(UserToNtkReq, "num-seamless-trees")
		NumSemTrees.text=("1")
		InterfacCap=ET.SubElement(talker, "interface-capabilities")
		VlanTagCap=ET.SubElement(InterfacCap, "vlan-tag-capable")
		VlanTagCap.text = ("true")
		Listeners=ET.SubElement(stream, "listeners")
		Index2= ET.SubElement(Listeners, "index")
		Listener=ET.SubElement(Listeners,"listener")
		EndStainter2=ET.SubElement(Listener, "end-station-interfaces")
		Mac2=ET.SubElement(EndStainter2, "mac-address")
		IntName=ET.SubElement(EndStainter2, "interface-name")
		UserToNtkReq2=ET.SubElement(Listener, "user-to-network-requirements")
		InterfacCap2=ET.SubElement(Listener, "interface-capabilities")
		VlanTagCap=ET.SubElement(InterfacCap2, "vlan-tag-capable")

	Qcctree = ET.ElementTree(Root_Qcc)
	Qcctree.write(Qcc, pretty_print=True)
	
################## Main Function ####################
if __name__ == "__main__":
	GeneratQcc("Qcc.xml")


