import random
import numpy as np
from lxml import etree as ET
import lxml.etree
from xml.dom.minidom import parseString
import csv

###Global Variabl declaration####
Num_End_Device=4

Num_Bridges= 2

TotalNum_Pub_App=int(random.gauss(20,1))
TotalNum_Sub_App=50

NumTotalDP=16
NumTotalRP=50

################### List Variables #################
TotalDevice_List=[]

DeviceListSubcrb=[]
DeviceList_Publish=[]
Num_DP_Per_App_List=[]
Num_RP_Per_App_List=[]
Ap_DP_Pair=[]

DP_List=[]
AppID_List=[]
Ass_DP_List=[]
Ass_DP_List_of_List=[]
Ass_DP_Param_Size =[]
Ass_DP_Param_List_of_List =[]
Ass_DP_TIM = []
Ass_DP_TIM_List_of_List = []

ParameterSize =[]

#w, h = 8, 5
#DP_List = [[0 for x in range(w)] for y in range(h)] 

############### Randome Number of App Generation ####
for i in range(TotalNum_Pub_App):        # Publishing App
	AppID_List.append(i+1)
	Num_DP_Per_App_List.append (int(random.gauss(10,2)))
	#App_list.append(MyApp(AppID_List, Num_DP_Per_App))

############### Randome Number of Subscribers ####
for i in range(TotalNum_Sub_App):        # Publishing App
	AppID_List.append(i+1)
	Num_RP_Per_App_List.append (int(random.gauss(NumTotalRP,2)))
	#App_list.append(MyApp(AppID_List, Num_DP_Per_App))

####### Parsing RT Tologogy ########################
with open("rt.xml", "r") as f:
    data = f.read()
tree = ET.parse('rt.xml')
root = tree.getroot()

for i in range (19):
	TotalDevice_List.append(root[i][0].text)
#print (TotalDevice_List)

#for elem in tree.iter():
#	print (elem)

#for elem in tree.iter():
    #print(elem.tag, elem.text)

#for tag in root_node.find_all(level):
    #value = tag.get(attribute)
    #if value is not None: print(value)

####### Parsing Qcc file ########################
with open("qccv1.xml", "r") as f:
	qccv1 = f.read()
qcc= ET.parse('qccv1.xml')

#for elem in qcc.iter():
	#print(elem.tag, elem.text)
	#if "stream-id"==:
	#	print ("Yes, we got it!")
	#print(elem.tag)
	
############Publishing Device Identification#####
#for i in range (len(TotalDevice_List))
DeviceList_Publish.append(TotalDevice_List[0])
DeviceList_Publish.append(TotalDevice_List[2])
DeviceListSubcrb.append(TotalDevice_List[1])
DeviceListSubcrb.append(TotalDevice_List[3])

#print(TotalDevice_List[2])
	
################### App Generation ##################
def GenerateApp(Parameter_Level_ICD, Stream_Level_ICD_V1) :
	root = ET.Element("Parameter-Level-ICD")
	Str_root= ET.Element("Stream-Level-ICD")

	index=0;
	for i in range (TotalNum_Pub_App):
		App1 = ET.SubElement(root, "Application", Name= "TSNApp"+str(AppID_List[i]))
		App2 = ET.SubElement(Str_root, "Application", Name= "TSNApp"+str(AppID_List[i]))
		Port = ET.SubElement(App1, "DeployedDevice", DeviceName= DeviceList_Publish[i%len(DeviceList_Publish)])
		Port2 = ET.SubElement(App2, "DeployedDevice", DeviceName= DeviceList_Publish[i%len(DeviceList_Publish)])
		DP1 = ET.SubElement(App1, "Port", Name="eth0")
		iii=1
		ParamSizSum1=0
		ParamSizSum2=0
		ParamSizSum3=0
		for j in range (Num_DP_Per_App_List[i]):
			ParameterSize.append(pow (2, int(random.gauss(2,1))))

		for k in range (Num_DP_Per_App_List[i]):
			if k<5:
				ParamSizSum1=ParamSizSum1+ParameterSize[index+k]
			elif 4<k<10:
				ParamSizSum2=ParamSizSum2+ParameterSize[index+k]
				#print (ParamSizSum2)
			elif 9<k<15:
				ParamSizSum3=ParamSizSum3+ParameterSize[index+k]

		Ass_DP_List=[]
		Ass_DP_Param_Size=[]
		Ass_DP_TIM =[]
				
				
		SDP1 = ET.SubElement(App2, "Port", Name="eth0")
		Stream=ET.SubElement(SDP1, "Stream", Name = "Stream"+str(AppID_List[i])+"-"+str(iii), ID=str(AppID_List[i]),FramesPerPeriod="1", MaxFrameSize=str(50+ParamSizSum1), RefreshPeriod="10")
		for j in range (Num_DP_Per_App_List[i]):
			transmissionIntervalMinimum=10+10*int(random.gauss(2,1))
			ET.SubElement(DP1, "DP", Name="DP"+str(j+index), ParameterSize= str(ParameterSize[index+j]), transmissionIntervalMinimum=str(transmissionIntervalMinimum))
			DP_List.append(str(j+index))
			if j%5==0 and j!=0: #int (Num_DP_Per_App[i]%2
				iii=iii+1
				Stream=ET.SubElement(SDP1, "Stream", Name = "Stream"+str(AppID_List[i])+"-"+str(iii), ID=str(AppID_List[i]+1),FramesPerPeriod="1", MaxFrameSize=str(50+ParamSizSum2), RefreshPeriod="10")
			#print ("DP-AP",AppID_List[i%len(AppID_List)], ":=", DP_List[(index+j)])
			
			ET.SubElement(Stream, "DP", Name="DP"+str(j+index), ParameterSize= str(ParameterSize[j+index]), transmissionIntervalMinimum=str(transmissionIntervalMinimum))
			Ap_DP_Pair.append("TSNApp"+str(AppID_List[i%len(AppID_List)])+".DP"+str(DP_List[(index+j)]))
			Ass_DP_List.append("DP"+str(j+index))
			Ass_DP_Param_Size.append (ParameterSize[index+j])
			Ass_DP_TIM.append(transmissionIntervalMinimum)
			
		index=index+Num_DP_Per_App_List[i]
		Ass_DP_List_of_List.append(Ass_DP_List)
		Ass_DP_Param_List_of_List.append(Ass_DP_Param_Size)
		Ass_DP_TIM_List_of_List.append(Ass_DP_TIM)
	
	index=0
	RPindex=0
	#print (Ap_DP_Pair)
	
############################### Listening Apps ########################
	for ii in range(TotalNum_Sub_App):
		App11 = ET.SubElement(root, "Appliction", Name= "TSNApp"+str(ii+1+len (AppID_List)))   #+str((Sub_List[i]+1)%len(Sub_List)) )
		Port1 = ET.SubElement(App11, "DeployedDevice", DeviceName=DeviceListSubcrb[ii%len(DeviceListSubcrb)]) #"+str(DeviceListSubcrb[i]))
		RP = ET.SubElement(App11, "Port", Name="eth0")
		for jj in range (Num_RP_Per_App_List[ii]):
			#jj%
			RubRef=ET.SubElement(RP, "RP", Name="RP_DP"+str(jj+RPindex))
			#print ("AP-RP", AppID_List[ii%len(AppID_List)], ":=", DP_List[(RPindex+jj)%len(DP_List)])
			#ET.SubElement(RubRef, "Pub_Ref", SrcName="TSNApp"+str(AppID_List[ii%len(AppID_List)])+".DP"+str(DP_List[(jj+RPindex)%len(DP_List)]))#+str(ii)#+str(App_list[i%(len(App_list))].ID)+".DP"+str(DP_ID[j1+index1]))
			ET.SubElement(RubRef, "Pub_Ref", SrcName=str(Ap_DP_Pair[(jj+RPindex)%len(Ap_DP_Pair)]))  #+str(Ap_DP_Pair[jj+RPindex]%len(Ap_DP_Pair)))
			
		if (ii%len(AppID_List)==0):
			index=0
			RPindex=0
		index=index+Num_DP_Per_App_List[ii%len(Num_DP_Per_App_List)]
		RPindex=RPindex+Num_DP_Per_App_List[ii%len(Num_DP_Per_App_List)]

	tree = ET.ElementTree(root)
	tree.write(Parameter_Level_ICD, pretty_print=True)
		
	treeStr = ET.ElementTree(Str_root)
	treeStr.write(Stream_Level_ICD_V1, pretty_print=True)

############################### Statistical Summary ####################
	data =[]
	header = ['App ID', 'Associated Device ID', '# of Associated DPs', 'list of associated DPs', 'sizes of associated DPS', 'rates of associated DPs']
	

	with open('Stat_Summary.csv', 'w', encoding='UTF8') as f:
		writer = csv.writer(f)
    # write the header
		writer.writerow(header)
    # write the data
		for a in range (TotalNum_Pub_App):
			data.append([AppID_List[a], DeviceList_Publish[a%len(DeviceList_Publish)], Num_DP_Per_App_List[a], Ass_DP_List_of_List[a], Ass_DP_Param_List_of_List[a], Ass_DP_TIM_List_of_List[a]]) # Num_DP_Per_App[i]+1, Ass_DP_List_of_List[i], Ass_DP_Param_List_of_List[i], Ass_DP_TIM_List_of_List[i]])
		for b in range(TotalNum_Pub_App):
			writer.writerow(data[b])

####### Reading Stream Level ICD ########################
with open("Stream_Level_ICD_V1.xml", "r") as f:
	stream = f.read()
stream= ET.parse('Stream_Level_ICD_V1.xml')
root = stream.getroot()
#xml = lxml.etree.parse('Stream_Level_ICD_V1.xml')

TotalNumStreams=0
ListOfStreams=[]
ListOfIDs = []
ListOfFramesPerPeriod=[]
ListOfMaxFrameSize =[]
ListOfRefreshPeriod =[]
########################Total Number of Streams###################
for elem in stream.iter():
		if (elem.tag=="Stream"):
			#print (elem.tag, elem.attrib) 
			TotalNumStreams=TotalNumStreams+1

for j in range (5): 
	ListOfTemp=[]
	for elem in stream.iter():
		if (elem.tag=="Stream"):
			#print (elem.tag, elem.attrib) 
			TotalNumStreams=TotalNumStreams+1
			my_list=str(elem.attrib).split(',')
			myStreamname= my_list[j].split(':')
			myStreamname.remove(myStreamname[0])
			strg=myStreamname[0]
			new_string = strg.replace("'", '')
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

#root = xml.getroot()
#print (root.find('./Stream').attrib['Name'])

#print(root.tag)
print(root[0].tag)
print(root[0].attrib)
print(root[0][0].attrib)
print(root[1].attrib)
print(root[1][0].attrib)
#print(root[1][0][0].attrib)

print(root[0][1][0].attrib)
old_string=str(root[0][1][0].attrib)
my_list=str(root[0][1][0].attrib).split(',')
myStreamname= my_list[0].split(':')
myStreamname.remove(myStreamname[0])
strg=myStreamname[0]

new_string = strg.replace("'", '')

SisStr='Sis'
#new_string = old_string.replace('FramesPerPeriod', '')
print(new_string)
print(root[1][1].attrib)
#print(root[1][0].attrib)




#xml.find('./Stream').attrib['Name']
#Stream1-1
#if == elem.tag and elem.text=='0':
#print ("Yes, we got it!")
	
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
		SrcIP.text=("10.1.1.11")
		DstIP= ET.SubElement (IpTup, "destination-ip-address")
		DstIP.text=("10.1.1.12")
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
	


######################### Main Function ####################################

################## Main Function ####################
if __name__ == "__main__":
	rd=int(random.gauss(TotalNum_Pub_App, 1))
	GenerateApp(("Parameter_Level_ICD.xml"),("Stream_Level_ICD_V1.xml"))
	#GenerateStream();

	GeneratQcc("Qcc.xml")
	

	