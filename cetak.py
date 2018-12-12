#!/usr/bin/python
#import copy
ryfcompatible=0
# ==================================================================
# RDF, konversi dari PHPPDF + ryf interpretter, generasi baru RYF
# Oleh : Ryan Widi Saputra
# Contact: ryannining@yahoo.com phone:08882521295
# File font yang diikutkan: arial,times,courier
# scanner and parser for script
#
# RDF, a PHPPDF conversion, with ryf interpretter and a ryf scripting
# engine is an ultimate Python Report generation tools.
# for more about ryf ,please go to sourceforge.net
#
# ==================================================================

# ==================================================================
# PYTHON SCRIPTING ENGINE
# An engine to simplify python scripting that mixed with ryf scripting
# please see the sample to fully understand what i mean
# ==================================================================
def getjpegsize(filename):
    # find pixel width and height of image
    # located at offset 5,6 (highbyte,lowbyte) and 7,8 after FF C0 or FF C2 marker
    f=file(filename,'rb')
    data=f.read(1024)
    f.close()
    for k in range(len(data)-1):
        if data[k] == chr(0xFF) and (data[k+1] == chr(0xC0) or data[k+1] == chr(0xC2)):
            height = ord(data[k+5])*256 + ord(data[k+6])
            width = ord(data[k+7])*256 + ord(data[k+8])
            return width,height
    return 0,0

# ==================================================================
# PYTHON PDF ENGINE
# An engine to create PDF
# please see the sample to fully understand what i mean
# ==================================================================

fontdict={'times new roman':'times',
          'times new roman bold':'timesB',
          'times new roman italic':'timesI',
          'times new roman bold italic':'timesBI',
          'arial':'helvetica',
          'arial bold':'helveticaB',
          'arial italic':'helveticaI',
          'arial bold italic':'helveticaBI',
          'symbol':'zapfdingbats'}
pdfviewer='evince'
def substr(s,i,j):
    return s[i:i+j]
def filesize(fn):
    try:
        c=file(fn)
        c.seek(0,2)
        fs=c.tell()
        c.close()
        return fs
    except:
        return 0
def fopen(fn,wm):
    return file(fn,wm)
def fread(f,size=None):
    if size:
        return f.read(size)
    return f.read()
def fwrite(f,buff,size=None):
    f.write(buff)
def fclose(f):
    f.close()
def str_replace(old,new,sstr):
    return sstr.replace(old,new)
def com(x,r=3):
    x=round(x,r)
    if int(x)==x:return int(x)
    return x
class tpdf:
    def __init__(this,orientation="P",unit="mm",format="A4"):
      this.page=0              #current page number
      this.offsets={}          #array of object offsets
      this.buffer=0            #buffer holding in-memory PDF
      this.pages=0             #array containing pages
      this.state=0             #current document state
      this.DefOrientation=0    #default orientation
      this.CurOrientation=0    #current orientation
      this.OrientationChanges=0#array indicating orientation changes
      this.fwPt,this.fhPt=0,0       #dimensions of page format in points
      this.fw,this.fh=0,0           #dimensions of page format in user unit
      this.wPt,this.hPt=0,0         #current dimensions of page in points
      this.w,h=0,0             #current dimensions of page in user unit
      this.x,this.y=0,0             #current position in user unit for cell positioning
      this.lasth=0             #height of last cell printed
      this.CoreFonts={}         #array of standard font names
      this.fonts={}            #array of used fonts
      this.ws=0                #word spacing
      this.ZoomMode=0          #zoom display mode
      this.LayoutMode=0        #layout display mode
      this.title=0             #title
      this.subject=0           #subject
      this.author=0            #author
      this.keywords=0          #keywords
      this.creator=0           #creator
      this.AliasNbPages=[]      #alias for total number of pages
      #Some checks
      this._dochecks()
      #Initialization of properties
      this.page=0
      this.n=2
      this.buffer=""
      this.pages={}
      this.OrientationChanges={}
      this.state=0
      this.fonts={}
      this.images={}
      this.lasth=0
      this.lcolor=0
      this.lw=0
      this.pdf_charwidths=pdf_charwidths
      this.ws=0
      this.afonts=[]
      #Standard fonts
      this.CoreFonts={"courier":"Courier","courierB":"Courier-Bold","courierI":"Courier-Oblique","courierBI":"Courier-BoldOblique",
            "helvetica":"Helvetica","helveticaB":"Helvetica-Bold","helveticaI":"Helvetica-Oblique","helveticaBI":"Helvetica-BoldOblique",
            "times":"Times-Roman","timesB":"Times-Bold","timesI":"Times-Italic","timesBI":"Times-BoldItalic",
            "symbol":"Symbol","zapfdingbats":"ZapfDingbats"}
      #Scale factor
      if(type(format) is str):
            format=format.lower()
            if   (format=="a3"):format=(841.89,1190.55)
            elif (format=="a4"):format=(595.28,841.89)
            elif (format=="a5"):format=array(420.94,595.28)
            elif (format=="letter"):format=array(612,792)
            elif (format=="legal"):format=array(612,1008)
            this.fwPt=format[0]
            this.fhPt=format[1]
      else:
            this.fwPt=format[0]
            this.fhPt=format[1]
            
      this.fw=this.fwPt;
      this.fh=this.fhPt;
      #Page orientation
      orientation=orientation.lower()
      if(orientation=="p" or orientation=="portrait"):
            this.DefOrientation="P"
            this.wPt=this.fwPt
            this.hPt=this.fhPt
      elif (orientation=="l" or orientation=="landscape"):
            this.DefOrientation="L"
            this.wPt=this.fhPt
            this.hPt=this.fwPt
      this.CurOrientation=this.DefOrientation;
      this.w=this.wPt
      this.h=this.hPt
    def SetTitle(this,title):
      this.title=title;
    def SetSubject(this,subject):
      this.subject=subject;
    def SetAuthor(this,author):
      this.author=author;
    def SetKeywords(this,keywords):
      this.keywords=keywords;
    def SetCreator(this,creator):
      this.creator=creator;
    def Open(this):
      #Begin document
      if(this.state==0):
            this._begindoc()

    def Close(this):
      #Terminate document
      if(this.state==3):
            return;
      if(this.page==0):
            this.AddPage()
      this._endpage()
      #Close document
      this._enddoc()
    def AddPage(this,orientation=""):
      #Start a new page
      this.activeFont=0
      if(this.state==0):this.Open()
      #Start new page
      this._beginpage(orientation)
      #Set line cap style to square
      this._out("2 J")
      #Page header
    def PageNo(this):
      return this.page;
    def SetDrawColor(this,r,g=-1,b=-1):
      #Set color for all stroking operations
      if((r==0 and g==0 and b==0) or g==-1):
            DrawColor="%s G" % com(r/255.0)
      else:
            DrawColor="%s %s %s RG" % (com(r/255.0),com(g/255.0),com(b/255.0))
      this._out(DrawColor)
    def SetFillColor(this,r,g=-1,b=-1):
      #Set color for all filling operations
      if(r==g and r==b):
            if r==0:FillColor='0 g'  
            else:FillColor="%s g" % com(r/255.0)
      else:
            FillColor="%s %s %s rg" % (com(r/255.0),com(g/255.0),com(b/255.0))
      this._out(FillColor)
    def TextSize(this,s,font=None):
      if font==None:font=this.afonts[-1]  
      #Get width of a string in the current font
      s=str(s)
      cw=font[0]["cw"]
      w=0
      for si in s:
          if si in cw:w+=cw[si]
          else:w=w+cw[' ']
      return (w*font[3]/1000.0,font[3])
    def SetLineWidth(this,width):
      #Set line width
      if(this.page>0):
            this._out("%s w" % com(width,1))

    def Line(this,x1,y1,x2,y2):
      #Draw a line
      this._out("%s %s m %s %s l S" % (com(x1,1),com(this.h-y1,1),com(x2,1),com(this.h-y2,1)))
    def Rect(this,x,y,w,h,style=""):
      #Draw a rectangle
      if(style=="F"):
            op="f";
      elif (style=="FD" or style=="DF"):
            op="B";
      else:
            op="S";
      this._out("%s %s %s %s re %s" % (com(x,1),com(this.h-y,1),com(w,1),com(-h,1),op))
    def lastFont(this):
        return this.afonts[-1]
    def setFont(this,family,style,size,color,activate=0):
      #Select a font; size given in points
      family=family.lower()
      if family in fontdict:family=fontdict[family]
      if family=="zapfdingbats":style=""
      ostyle=style
      style=style.upper()
      if "U" in style:
            this.underline=True;
            style=style.replace("U","")
      else:
            this.underline=False
      if(style=="IB"):style="BI"
      fontkey=family+style;
      if not(fontkey in this.CoreFonts):fontkey='times'
      if(not fontkey in this.fonts):
          i=len(this.fonts)+1;
          this.fonts[fontkey]={"i":i,"type":"core",
                                     "name":this.CoreFonts[fontkey],
                                     "up":-100,"ut":50,
                                     "cw":this.pdf_charwidths[fontkey]}
      if not (type(color) is str):
          r=color[0]  
          g=color[1]  
          b=color[2]  
          if(r==g and r==b):
                if r==0:color='0 g'  
                else:color="%s g" % com(r/255.0)
          else:
                color="%s %s %s rg" % (com(r/255.0),com(g/255.0),com(b/255.0))
      fontob=[this.fonts[fontkey],family,ostyle,size,color]
      this.afonts.append(fontob)
      if activate:this.activateFont(fontob)
    def activateFont(this,fontob):
      if this.activeFont<>fontob:
          col=fontob[4]
          this._out("/F%d %s Tf" % (fontob[0]["i"],com(fontob[3],1)))
          if this.lcolor<>col:this._out(col)
          this.activeFont=fontob
          this.lcolor=col
    def prevFont(this):  
      del this.afonts[-1]
    def BeginText(this,x,y,w=0):
        this._out("BT %s %s Td" %(com(x,1),com(this.h-y,1)))
        if w<>this.lw:this._out("%s Tw" %(com(w,3)))
        this.lw=w
    def TextXY(this,x,y):
      this._out("ET BT %s %s Td" %(com(x,1),com(this.h-y,1)))
    def Text(this,txt,x=0,y=0):
      if x or y:this._out("%s %s Td" %(com(x,1),com(this.h-y,1)))
      this._out("(%s) Tj" %this._escape(txt))
    def EndText(this):
        this._out("ET")
    def TextOut(this,x,y,txt):
      font=this.activeFont
      sty=font[1]
      s="BT %s %s Td (%s) Tj ET" %(com(x,1),com(this.h-y,1),this._escape(txt))
      if('U' in sty) and txt:s+=" "+this._dounderline(x,y,txt)
      this._out(s)
    def Image(this,filename,x,y,w=0,h=0):
        #Put an image on the page
        if not(filename in this.images):
            #First use of image, get info
            tipe=filename.split('.')[1].lower()
            if tipe in ['.jpg','.jpeg']:
                info=this._parsejpg(filename)
            elif tipe == '.png':
                info=this._parsepng(filename)
            else:return            
            info['i']=len(this.images)+1
            this.images[filename]=info
        else:
            info=this.images[filename]
        if(w==0 and h==0):
            w=info['w']
            h=info['h']
        if(w==0):
            w=h*info['w']/info['h']
        if(h==0):
            h=w*info['h']/info['w']
        this._out('q %s 0 0 %s %s %s cm /I%s Do Q' % (com(w),com(h),com(x),com(this.h-(y+h)),info['i']))
#        if($link)
#            this.Link($x,$y,$w,$h,$link);
        return w,h
    def Output(this,name="",dest=""):
      if(this.state<3):this.Close()
      return this.buffer;
    def Error(this,x):
        print x
    def _parsejpg(this,filename):
        #Extract info from a JPEG file
        w,h=getjpegsize(filename)
        if not(w+h):
            print 'Missing or incorrect image file: ',filename
            return
        colspace='DeviceRGB'
        bpc=8
        #Read whole file
        f=file(filename,'rb')
        data=f.read()
        f.close()
        return {'w':w,'h':h,'cs':colspace,'bpc':bpc,'f':'DCTDecode','data':data}
    def _freadint(this,f):
        #Read a 4-byte integer from file
        i=ord(f.read(1))<<24
        i+=ord(f.read(1))<<16
        i+=ord(f.read(1))<<8
        i+=ord(f.read(1))
        return i
    def _parsepng(this,filename):
        #Extract info from a PNG file
        f=file(filename,'rb')
        #Check signature
        if f.read(8)<>(chr(137)+'PNG'+chr(13)+chr(10)+chr(26)+chr(10)):
           this.Error('Not PNG file: %s'%filename)
           return
        #Read header chunk
        f.read(4)
        if(f.read(4)<>'IHDR'):
            this.Error('Incorrect PNG file: %s'%filename)
            return
        w=this._freadint(f)
        h=this._freadint(f)
        bpc=ord(f.read(1))
        if(bpc>8):
            this.Error('16-bit depth not supported: %s'%filename)
        ct=ord(f.read(1))
        if(ct==0):colspace='DeviceGray'
        elif (ct==2):colspace='DeviceRGB'
        elif (ct==3):colspace='Indexed'
        else:
            this.Error('Alpha channel not supported: %s' % filename)
        if(ord(f.read(1))<>0):
            this.Error('Unknown compression method: %s'%filename)
        if(ord(f.read(1))<>0):
            this.Error('Unknown filter method: %s'%filename)
        if(ord(f.read(1))<>0):
            this.Error('Interlacing not supported: %s'%filename)
        f.read(4)
        parms='/DecodeParms <</Predictor 15 /Colors %s'%(int(ct==2)* 3 or 1)
        parms+=' /BitsPerComponent %s /Columns %s>>' %(bpc,w)
        #Scan chunks looking for palette, transparency and image data
        pal=''
        trns=''
        data=''
        while 1:
            n=this._freadint(f)
            if n==0:break
            tipe=f.read(4)
            if(tipe=='PLTE'):
                #Read palette
                pal=f.read(n);
                f.read(4)
            elif(tipe=='tRNS'):
                #Read transparency info
                t=f.read(n)
                if(ct==0):trns=array(ord(substr(t,1,1)));
                elif(ct==2):trns=array(ord(substr(t,1,1)),ord(substr(t,3,1)),ord(substr(t,5,1)));
                else:
                    pos=strpos(t,chr(0))
                    if chr(0) in t:
                        pos=t.index(chr(0))
                        trns=array(pos)
                f.read(4)
            elif(tipe=='IDAT'):
                #Read image data block
                data+=f.read(n)
                f.read(4)
            elif(tipe=='IEND'):
                break
            else:f.read(n+4)
        
        if(colspace=='Indexed' and not pal):
            this.Error('Missing palette in %s'%filename);
        f.close()
        return {'w':w,'h':h,'cs':colspace,'bpc':bpc,'f':'FlateDecode','parms':parms,'pal':pal,'trns':trns,'data':data}
    def _dochecks(this):
        pass
    def _begindoc(this):
      #Start document
      this.state=1;
      this._out("%PDF-1.3")

    def _putpages(this):
      nb=this.page;
      if(len(this.AliasNbPages)):
            #Replace number of pages
            for n in range(1,nb+1):
                  this.pages[n]=str_replace(this.AliasNbPages,str(nb),this.pages[n])
#                  this.pages[n]=str(n)
      if(this.DefOrientation=="P"):
            wPt=this.fwPt;
            hPt=this.fhPt;
      else:
            wPt=this.fhPt;
            hPt=this.fwPt;
      filter="";
      for n in range(1,nb+1):
            #Page
            this._newobj()
            this._out("<</Type /Page")
            this._out("/Parent 1 0 R")
            if(n in this.OrientationChanges):
                  this._out("/MediaBox [0 0 %s %s]" % (com(hPt,1),com(wPt,1)))
            this._out("/Resources 2 0 R")
            this._out("/Contents %s"%(this.n+1)+" 0 R>>")
            this._out("endobj")
            #Page content
            p=this.pages[n];
            this._newobj()
            this._out("<<"+filter+"/Length %s"%len(p)+">>")
            this._putstream(p)
            this._out("endobj")
      #Pages root
      this.offsets[1]=len(this.buffer)
      this._out("1 0 obj")
      this._out("<</Type /Pages")
      kids="/Kids [";
      for i in range(nb):
            kids+=str(3+2*i)+" 0 R ";
      this._out(kids+"]")
      this._out("/Count %s"%nb)
      this._out("/MediaBox [0 0 %s %s]" %(com(wPt,1),com(hPt,1)))
      this._out(">>")
      this._out("endobj")

    def _putfonts(this):
      nf=this.n;
      for k in this.fonts:
            font=this.fonts[k]
            #Font objects
            this.fonts[k]["n"]=this.n+1;
            type=font["type"];
            name=font["name"];
            if(type=="core"):
                  #Standard font
                  this._newobj()
                  this._out("<</Type /Font")
                  this._out("/BaseFont /"+name)
                  this._out("/Subtype /Type1")
                  if(name<>"Symbol" and name<>"ZapfDingbats"):
                        this._out("/Encoding /WinAnsiEncoding")
                  this._out(">>")
                  this._out("endobj")
            else:
                  #Allow for additional types
                  mtd="_put"+type.lower()
                  this.mtd(font)

    def _putimages(this):
        filter=''
        for filename in this.images:
            info=this.images[filename]
            this._newobj()
            info['n']=this.n
            this._out('<</Type /XObject')
            this._out('/Subtype /Image')
            this._out('/Width %s' % com(info['w']))
            this._out('/Height %s' % com(info['h']))
            this._out('/ColorSpace /'+info['cs'])
#            if(info['cs']=='DeviceCMYK'):this._out('/Decode [1 0 1 0 1 0 1 0]')
            this._out('/BitsPerComponent %s' % com(info['bpc']))
            this._out('/Filter /'+info['f'])
            if('parms' in info):this._out(info['parms'])
            this._out('/Length %s>>' % len(info['data']))
            this._putstream(info['data'])
            del info['data']
            this._out('endobj')
    def _putresources(this):
      this._putfonts()
      this._putimages()
      #Resource dictionary
      this.offsets[2]=len(this.buffer)
      this._out("2 0 obj")
      this._out("<</ProcSet [/PDF /Text /ImageB /ImageC /ImageI]")
      this._out("/Font <<")
      for font in this.fonts.values():
            this._out("/F%s"%font["i"]+" %s"%font["n"]+" 0 R")
      this._out(">>")
      if(this.images):
            this._out('/XObject <<')
            for f in this.images:
                image=this.images[f]
                this._out('/I%s %s 0 R' %(image['i'],image['n']))
            this._out('>>')
      this._out(">>")
      this._out("endobj")
    def _putinfo(this):
      this._out("/Producer "+this._textstring("RDF 0.1"))
      if(this.title):
            this._out("/Title "+this._textstring(this.title))
      if(this.subject):
            this._out("/Subject "+this._textstring(this.subject))
      if(this.author):
            this._out("/Author "+this._textstring(this.author))
      if(this.keywords):
            this._out("/Keywords "+this._textstring(this.keywords))
      if(this.creator):
            this._out("/Creator "+this._textstring(this.creator))
    def _putcatalog(this):
      this._out("/Type /Catalog")
      this._out("/Pages 1 0 R")
      if(this.ZoomMode=="fullpage"):
            this._out("/OpenAction [3 0 R /Fit]")
      elif(this.ZoomMode=="fullwidth"):
            this._out("/OpenAction [3 0 R /FitH null]")
      elif(this.ZoomMode=="real"):
            this._out("/OpenAction [3 0 R /XYZ null null 1]")
      elif(not type(this.ZoomMode) is str):
            this._out("/OpenAction [3 0 R /XYZ null null %s"%(this.ZoomMode/100)+"]")
      if(this.LayoutMode=="single"):
            this._out("/PageLayout /SinglePage")
      elif(this.LayoutMode=="continuous"):
            this._out("/PageLayout /OneColumn")
      elif(this.LayoutMode=="two"):
            this._out("/PageLayout /TwoColumnLeft")
    def _puttrailer(this):
      this._out("/Size %s"%(this.n+1))
      this._out("/Root %s"%this.n+" 0 R")
      this._out("/Info %s"%(this.n-1)+" 0 R")
    def _enddoc(this):
      this._putpages()
      this._putresources()
      #Info
      this._newobj()
      this._out("<<")
      this._putinfo()
      this._out(">>")
      this._out("endobj")
      #Catalog
      this._newobj()
      this._out("<<")
      this._putcatalog()
      this._out(">>")
      this._out("endobj")
      #Cross-ref
      o=len(this.buffer)
      this._out("xref")
      this._out("0 %s"%(this.n+1))
      this._out("0000000000 65535 f ")
      for i in range(1,this.n+1):
            this._out("%010d 00000 n " % (this.offsets[i]))
      #Trailer
      this._out("trailer")
      this._out("<<")
      this._puttrailer()
      this._out(">>")
      this._out("startxref")
      this._out(o)
      this._out("%%EOF")
      this.state=3;

    def _beginpage(this,orientation):
      this.page+=1;
      this.pages[this.page]="";
      this.state=2;
      this.x=0
      this.y=0
      this.FontFamily="";
      #Page orientation
      if(not orientation):
            orientation=this.DefOrientation;
      else:
            orientation=orientation[0].upper()
            if(orientation<>this.DefOrientation):
                  this.OrientationChanges[this.page]=True;
      #Change orientation
      if(orientation=="P"):
          this.wPt=this.fwPt;
          this.hPt=this.fhPt;
          this.w=this.fwPt;
          this.h=this.fhPt;
      else:
          this.wPt=this.fhPt;
          this.hPt=this.fwPt;
          this.w=this.fhPt;
          this.h=this.fwPt;
      this.CurOrientation=orientation;

    def _endpage(this):
      #End of page contents
      this.state=1;

    def _newobj(this):
      #Begin a new object
      this.n+=1;
      this.offsets[this.n]=len(this.buffer)
      this._out(str(this.n)+" 0 obj")

    def _dounderline(this,x,y,txt):
      #Underline text
      up=this.CurrentFont["up"];
      ut=this.CurrentFont["ut"];
      w=this.GetStringWidth(txt)+this.ws*substr_count(txt," ")
      return "%s %s %s %s re f" % (com(x,1),com(this.h-(y-up/1000*this.FontSize),1),
                                           com(w,1),com(-ut/1000*this.FontSizePt,1))

    def _textstring(this,s):
      #Format a text string
      return "("+this._escape(s)+")";

    def _escape(this,s):
      #Add \ before \, ( and )
      return str_replace(")","\\)",str_replace("(","\\(",str_replace("\\","\\\\",s)))

    def _putstream(this,s):
      this._out("stream")
      this._out(s)
      this._out("endstream")

    def _out(this,s):
      #Add a line to the document
      if(this.state==2):
            this.pages[this.page]+=str(s)+"\n";
      else:
            this.buffer+=str(s)+"\n";

# Courier
pdf_charwidths={}
pdf_charwidths["courier"]={}
for i in range(256):
	pdf_charwidths["courier"][chr(i)]=600;
pdf_charwidths["courierB"]=pdf_charwidths["courier"];
pdf_charwidths["courierI"]=pdf_charwidths["courier"];
pdf_charwidths["courierBI"]=pdf_charwidths["courier"];

# Helvetica
pdf_charwidths["helvetica"]={chr(0):278,chr(1):278,chr(2):278,chr(3):278,chr(4):278,chr(5):278,chr(6):278,chr(7):278,chr(8):278,chr(9):278,chr(10):278,chr(11):278,chr(12):278,chr(13):278,chr(14):278,chr(15):278,chr(16):278,chr(17):278,chr(18):278,chr(19):278,chr(20):278,chr(21):278,
	chr(22):278,chr(23):278,chr(24):278,chr(25):278,chr(26):278,chr(27):278,chr(28):278,chr(29):278,chr(30):278,chr(31):278," ":278,"!":278,"\"":355,"#":556,"$":556,"%":889,"&":667,"\"":191,"(":333,")":333,"*":389,"+":584,
	",":278,"-":333,".":278,"/":278,"0":556,"1":556,"2":556,"3":556,"4":556,"5":556,"6":556,"7":556,"8":556,"9":556,":":278,";":278,"<":584,"=":584,">":584,"?":556,chr(64):1015,"A":667,
	"B":667,"C":722,"D":722,"E":667,"F":611,"G":778,"H":722,"I":278,"J":500,"K":667,"L":556,"M":833,"N":722,"O":778,"P":667,"Q":778,"R":722,"S":667,"T":611,"U":722,"V":667,"W":944,
	"X":667,"Y":667,"Z":611,"[":278,"\\":278,"]":278,"^":469,"_":556,"`":333,"a":556,"b":556,"c":500,"d":556,"e":556,"f":278,"g":556,"h":556,"i":222,"j":222,"k":500,"l":222,"m":833,
	"n":556,"o":556,"p":556,"q":556,"r":333,"s":500,"t":278,"u":556,"v":500,"w":722,"x":500,"y":500,"z":500,"{":334,"|":260,"}":334,"~":584,chr(127):350,chr(128):556,chr(129):350,chr(130):222,chr(131):556,
	chr(132):333,chr(133):1000,chr(134):556,chr(135):556,chr(136):333,chr(137):1000,chr(138):667,chr(139):333,chr(140):1000,chr(141):350,chr(142):611,chr(143):350,chr(144):350,chr(145):222,chr(146):222,chr(147):333,chr(148):333,chr(149):350,chr(150):556,chr(151):1000,chr(152):333,chr(153):1000,
	chr(154):500,chr(155):333,chr(156):944,chr(157):350,chr(158):500,chr(159):667,chr(160):278,chr(161):333,chr(162):556,chr(163):556,chr(164):556,chr(165):556,chr(166):260,chr(167):556,chr(168):333,chr(169):737,chr(170):370,chr(171):556,chr(172):584,chr(173):333,chr(174):737,chr(175):333,
	chr(176):400,chr(177):584,chr(178):333,chr(179):333,chr(180):333,chr(181):556,chr(182):537,chr(183):278,chr(184):333,chr(185):333,chr(186):365,chr(187):556,chr(188):834,chr(189):834,chr(190):834,chr(191):611,chr(192):667,chr(193):667,chr(194):667,chr(195):667,chr(196):667,chr(197):667,
	chr(198):1000,chr(199):722,chr(200):667,chr(201):667,chr(202):667,chr(203):667,chr(204):278,chr(205):278,chr(206):278,chr(207):278,chr(208):722,chr(209):722,chr(210):778,chr(211):778,chr(212):778,chr(213):778,chr(214):778,chr(215):584,chr(216):778,chr(217):722,chr(218):722,chr(219):722,
	chr(220):722,chr(221):667,chr(222):667,chr(223):611,chr(224):556,chr(225):556,chr(226):556,chr(227):556,chr(228):556,chr(229):556,chr(230):889,chr(231):500,chr(232):556,chr(233):556,chr(234):556,chr(235):556,chr(236):278,chr(237):278,chr(238):278,chr(239):278,chr(240):556,chr(241):556,
	chr(242):556,chr(243):556,chr(244):556,chr(245):556,chr(246):556,chr(247):584,chr(248):611,chr(249):556,chr(250):556,chr(251):556,chr(252):556,chr(253):500,chr(254):556,chr(255):500}

pdf_charwidths["helveticaB"]={chr(0):278,chr(1):278,chr(2):278,chr(3):278,chr(4):278,chr(5):278,chr(6):278,chr(7):278,chr(8):278,chr(9):278,chr(10):278,chr(11):278,chr(12):278,chr(13):278,chr(14):278,chr(15):278,chr(16):278,chr(17):278,chr(18):278,chr(19):278,chr(20):278,chr(21):278,
	chr(22):278,chr(23):278,chr(24):278,chr(25):278,chr(26):278,chr(27):278,chr(28):278,chr(29):278,chr(30):278,chr(31):278," ":278,"!":333,"\"":474,"#":556,"$":556,"%":889,"&":722,"\"":238,"(":333,")":333,"*":389,"+":584,
	",":278,"-":333,".":278,"/":278,"0":556,"1":556,"2":556,"3":556,"4":556,"5":556,"6":556,"7":556,"8":556,"9":556,":":333,";":333,"<":584,"=":584,">":584,"?":611,chr(64):975,"A":722,
	"B":722,"C":722,"D":722,"E":667,"F":611,"G":778,"H":722,"I":278,"J":556,"K":722,"L":611,"M":833,"N":722,"O":778,"P":667,"Q":778,"R":722,"S":667,"T":611,"U":722,"V":667,"W":944,
	"X":667,"Y":667,"Z":611,"[":333,"\\":278,"]":333,"^":584,"_":556,"`":333,"a":556,"b":611,"c":556,"d":611,"e":556,"f":333,"g":611,"h":611,"i":278,"j":278,"k":556,"l":278,"m":889,
	"n":611,"o":611,"p":611,"q":611,"r":389,"s":556,"t":333,"u":611,"v":556,"w":778,"x":556,"y":556,"z":500,"{":389,"|":280,"}":389,"~":584,chr(127):350,chr(128):556,chr(129):350,chr(130):278,chr(131):556,
	chr(132):500,chr(133):1000,chr(134):556,chr(135):556,chr(136):333,chr(137):1000,chr(138):667,chr(139):333,chr(140):1000,chr(141):350,chr(142):611,chr(143):350,chr(144):350,chr(145):278,chr(146):278,chr(147):500,chr(148):500,chr(149):350,chr(150):556,chr(151):1000,chr(152):333,chr(153):1000,
	chr(154):556,chr(155):333,chr(156):944,chr(157):350,chr(158):500,chr(159):667,chr(160):278,chr(161):333,chr(162):556,chr(163):556,chr(164):556,chr(165):556,chr(166):280,chr(167):556,chr(168):333,chr(169):737,chr(170):370,chr(171):556,chr(172):584,chr(173):333,chr(174):737,chr(175):333,
	chr(176):400,chr(177):584,chr(178):333,chr(179):333,chr(180):333,chr(181):611,chr(182):556,chr(183):278,chr(184):333,chr(185):333,chr(186):365,chr(187):556,chr(188):834,chr(189):834,chr(190):834,chr(191):611,chr(192):722,chr(193):722,chr(194):722,chr(195):722,chr(196):722,chr(197):722,
	chr(198):1000,chr(199):722,chr(200):667,chr(201):667,chr(202):667,chr(203):667,chr(204):278,chr(205):278,chr(206):278,chr(207):278,chr(208):722,chr(209):722,chr(210):778,chr(211):778,chr(212):778,chr(213):778,chr(214):778,chr(215):584,chr(216):778,chr(217):722,chr(218):722,chr(219):722,
	chr(220):722,chr(221):667,chr(222):667,chr(223):611,chr(224):556,chr(225):556,chr(226):556,chr(227):556,chr(228):556,chr(229):556,chr(230):889,chr(231):556,chr(232):556,chr(233):556,chr(234):556,chr(235):556,chr(236):278,chr(237):278,chr(238):278,chr(239):278,chr(240):611,chr(241):611,
	chr(242):611,chr(243):611,chr(244):611,chr(245):611,chr(246):611,chr(247):584,chr(248):611,chr(249):611,chr(250):611,chr(251):611,chr(252):611,chr(253):556,chr(254):611,chr(255):556}

pdf_charwidths["helveticaBI"]={chr(0):278,chr(1):278,chr(2):278,chr(3):278,chr(4):278,chr(5):278,chr(6):278,chr(7):278,chr(8):278,chr(9):278,chr(10):278,chr(11):278,chr(12):278,chr(13):278,chr(14):278,chr(15):278,chr(16):278,chr(17):278,chr(18):278,chr(19):278,chr(20):278,chr(21):278,
	chr(22):278,chr(23):278,chr(24):278,chr(25):278,chr(26):278,chr(27):278,chr(28):278,chr(29):278,chr(30):278,chr(31):278," ":278,"!":333,"\"":474,"#":556,"$":556,"%":889,"&":722,"\"":238,"(":333,")":333,"*":389,"+":584,
	",":278,"-":333,".":278,"/":278,"0":556,"1":556,"2":556,"3":556,"4":556,"5":556,"6":556,"7":556,"8":556,"9":556,":":333,";":333,"<":584,"=":584,">":584,"?":611,chr(64):975,"A":722,
	"B":722,"C":722,"D":722,"E":667,"F":611,"G":778,"H":722,"I":278,"J":556,"K":722,"L":611,"M":833,"N":722,"O":778,"P":667,"Q":778,"R":722,"S":667,"T":611,"U":722,"V":667,"W":944,
	"X":667,"Y":667,"Z":611,"[":333,"\\":278,"]":333,"^":584,"_":556,"`":333,"a":556,"b":611,"c":556,"d":611,"e":556,"f":333,"g":611,"h":611,"i":278,"j":278,"k":556,"l":278,"m":889,
	"n":611,"o":611,"p":611,"q":611,"r":389,"s":556,"t":333,"u":611,"v":556,"w":778,"x":556,"y":556,"z":500,"{":389,"|":280,"}":389,"~":584,chr(127):350,chr(128):556,chr(129):350,chr(130):278,chr(131):556,
	chr(132):500,chr(133):1000,chr(134):556,chr(135):556,chr(136):333,chr(137):1000,chr(138):667,chr(139):333,chr(140):1000,chr(141):350,chr(142):611,chr(143):350,chr(144):350,chr(145):278,chr(146):278,chr(147):500,chr(148):500,chr(149):350,chr(150):556,chr(151):1000,chr(152):333,chr(153):1000,
	chr(154):556,chr(155):333,chr(156):944,chr(157):350,chr(158):500,chr(159):667,chr(160):278,chr(161):333,chr(162):556,chr(163):556,chr(164):556,chr(165):556,chr(166):280,chr(167):556,chr(168):333,chr(169):737,chr(170):370,chr(171):556,chr(172):584,chr(173):333,chr(174):737,chr(175):333,
	chr(176):400,chr(177):584,chr(178):333,chr(179):333,chr(180):333,chr(181):611,chr(182):556,chr(183):278,chr(184):333,chr(185):333,chr(186):365,chr(187):556,chr(188):834,chr(189):834,chr(190):834,chr(191):611,chr(192):722,chr(193):722,chr(194):722,chr(195):722,chr(196):722,chr(197):722,
	chr(198):1000,chr(199):722,chr(200):667,chr(201):667,chr(202):667,chr(203):667,chr(204):278,chr(205):278,chr(206):278,chr(207):278,chr(208):722,chr(209):722,chr(210):778,chr(211):778,chr(212):778,chr(213):778,chr(214):778,chr(215):584,chr(216):778,chr(217):722,chr(218):722,chr(219):722,
	chr(220):722,chr(221):667,chr(222):667,chr(223):611,chr(224):556,chr(225):556,chr(226):556,chr(227):556,chr(228):556,chr(229):556,chr(230):889,chr(231):556,chr(232):556,chr(233):556,chr(234):556,chr(235):556,chr(236):278,chr(237):278,chr(238):278,chr(239):278,chr(240):611,chr(241):611,
	chr(242):611,chr(243):611,chr(244):611,chr(245):611,chr(246):611,chr(247):584,chr(248):611,chr(249):611,chr(250):611,chr(251):611,chr(252):611,chr(253):556,chr(254):611,chr(255):556}

pdf_charwidths["helveticaI"]={chr(0):278,chr(1):278,chr(2):278,chr(3):278,chr(4):278,chr(5):278,chr(6):278,chr(7):278,chr(8):278,chr(9):278,chr(10):278,chr(11):278,chr(12):278,chr(13):278,chr(14):278,chr(15):278,chr(16):278,chr(17):278,chr(18):278,chr(19):278,chr(20):278,chr(21):278,
	chr(22):278,chr(23):278,chr(24):278,chr(25):278,chr(26):278,chr(27):278,chr(28):278,chr(29):278,chr(30):278,chr(31):278," ":278,"!":278,"\"":355,"#":556,"$":556,"%":889,"&":667,"\"":191,"(":333,")":333,"*":389,"+":584,
	",":278,"-":333,".":278,"/":278,"0":556,"1":556,"2":556,"3":556,"4":556,"5":556,"6":556,"7":556,"8":556,"9":556,":":278,";":278,"<":584,"=":584,">":584,"?":556,chr(64):1015,"A":667,
	"B":667,"C":722,"D":722,"E":667,"F":611,"G":778,"H":722,"I":278,"J":500,"K":667,"L":556,"M":833,"N":722,"O":778,"P":667,"Q":778,"R":722,"S":667,"T":611,"U":722,"V":667,"W":944,
	"X":667,"Y":667,"Z":611,"[":278,"\\":278,"]":278,"^":469,"_":556,"`":333,"a":556,"b":556,"c":500,"d":556,"e":556,"f":278,"g":556,"h":556,"i":222,"j":222,"k":500,"l":222,"m":833,
	"n":556,"o":556,"p":556,"q":556,"r":333,"s":500,"t":278,"u":556,"v":500,"w":722,"x":500,"y":500,"z":500,"{":334,"|":260,"}":334,"~":584,chr(127):350,chr(128):556,chr(129):350,chr(130):222,chr(131):556,
	chr(132):333,chr(133):1000,chr(134):556,chr(135):556,chr(136):333,chr(137):1000,chr(138):667,chr(139):333,chr(140):1000,chr(141):350,chr(142):611,chr(143):350,chr(144):350,chr(145):222,chr(146):222,chr(147):333,chr(148):333,chr(149):350,chr(150):556,chr(151):1000,chr(152):333,chr(153):1000,
	chr(154):500,chr(155):333,chr(156):944,chr(157):350,chr(158):500,chr(159):667,chr(160):278,chr(161):333,chr(162):556,chr(163):556,chr(164):556,chr(165):556,chr(166):260,chr(167):556,chr(168):333,chr(169):737,chr(170):370,chr(171):556,chr(172):584,chr(173):333,chr(174):737,chr(175):333,
	chr(176):400,chr(177):584,chr(178):333,chr(179):333,chr(180):333,chr(181):556,chr(182):537,chr(183):278,chr(184):333,chr(185):333,chr(186):365,chr(187):556,chr(188):834,chr(189):834,chr(190):834,chr(191):611,chr(192):667,chr(193):667,chr(194):667,chr(195):667,chr(196):667,chr(197):667,
	chr(198):1000,chr(199):722,chr(200):667,chr(201):667,chr(202):667,chr(203):667,chr(204):278,chr(205):278,chr(206):278,chr(207):278,chr(208):722,chr(209):722,chr(210):778,chr(211):778,chr(212):778,chr(213):778,chr(214):778,chr(215):584,chr(216):778,chr(217):722,chr(218):722,chr(219):722,
	chr(220):722,chr(221):667,chr(222):667,chr(223):611,chr(224):556,chr(225):556,chr(226):556,chr(227):556,chr(228):556,chr(229):556,chr(230):889,chr(231):500,chr(232):556,chr(233):556,chr(234):556,chr(235):556,chr(236):278,chr(237):278,chr(238):278,chr(239):278,chr(240):556,chr(241):556,
	chr(242):556,chr(243):556,chr(244):556,chr(245):556,chr(246):556,chr(247):584,chr(248):611,chr(249):556,chr(250):556,chr(251):556,chr(252):556,chr(253):500,chr(254):556,chr(255):500}

pdf_charwidths["symbol"]={chr(0):250,chr(1):250,chr(2):250,chr(3):250,chr(4):250,chr(5):250,chr(6):250,chr(7):250,chr(8):250,chr(9):250,chr(10):250,chr(11):250,chr(12):250,chr(13):250,chr(14):250,chr(15):250,chr(16):250,chr(17):250,chr(18):250,chr(19):250,chr(20):250,chr(21):250,
	chr(22):250,chr(23):250,chr(24):250,chr(25):250,chr(26):250,chr(27):250,chr(28):250,chr(29):250,chr(30):250,chr(31):250," ":250,"!":333,"\"":713,"#":500,"$":549,"%":833,"&":778,"\"":439,"(":333,")":333,"*":500,"+":549,
	",":250,"-":549,".":250,"/":278,"0":500,"1":500,"2":500,"3":500,"4":500,"5":500,"6":500,"7":500,"8":500,"9":500,":":278,";":278,"<":549,"=":549,">":549,"?":444,chr(64):549,"A":722,
	"B":667,"C":722,"D":612,"E":611,"F":763,"G":603,"H":722,"I":333,"J":631,"K":722,"L":686,"M":889,"N":722,"O":722,"P":768,"Q":741,"R":556,"S":592,"T":611,"U":690,"V":439,"W":768,
	"X":645,"Y":795,"Z":611,"[":333,"\\":863,"]":333,"^":658,"_":500,"`":500,"a":631,"b":549,"c":549,"d":494,"e":439,"f":521,"g":411,"h":603,"i":329,"j":603,"k":549,"l":549,"m":576,
	"n":521,"o":549,"p":549,"q":521,"r":549,"s":603,"t":439,"u":576,"v":713,"w":686,"x":493,"y":686,"z":494,"{":480,"|":200,"}":480,"~":549,chr(127):0,chr(128):0,chr(129):0,chr(130):0,chr(131):0,
	chr(132):0,chr(133):0,chr(134):0,chr(135):0,chr(136):0,chr(137):0,chr(138):0,chr(139):0,chr(140):0,chr(141):0,chr(142):0,chr(143):0,chr(144):0,chr(145):0,chr(146):0,chr(147):0,chr(148):0,chr(149):0,chr(150):0,chr(151):0,chr(152):0,chr(153):0,
	chr(154):0,chr(155):0,chr(156):0,chr(157):0,chr(158):0,chr(159):0,chr(160):750,chr(161):620,chr(162):247,chr(163):549,chr(164):167,chr(165):713,chr(166):500,chr(167):753,chr(168):753,chr(169):753,chr(170):753,chr(171):1042,chr(172):987,chr(173):603,chr(174):987,chr(175):603,
	chr(176):400,chr(177):549,chr(178):411,chr(179):549,chr(180):549,chr(181):713,chr(182):494,chr(183):460,chr(184):549,chr(185):549,chr(186):549,chr(187):549,chr(188):1000,chr(189):603,chr(190):1000,chr(191):658,chr(192):823,chr(193):686,chr(194):795,chr(195):987,chr(196):768,chr(197):768,
	chr(198):823,chr(199):768,chr(200):768,chr(201):713,chr(202):713,chr(203):713,chr(204):713,chr(205):713,chr(206):713,chr(207):713,chr(208):768,chr(209):713,chr(210):790,chr(211):790,chr(212):890,chr(213):823,chr(214):549,chr(215):250,chr(216):713,chr(217):603,chr(218):603,chr(219):1042,
	chr(220):987,chr(221):603,chr(222):987,chr(223):603,chr(224):494,chr(225):329,chr(226):790,chr(227):790,chr(228):786,chr(229):713,chr(230):384,chr(231):384,chr(232):384,chr(233):384,chr(234):384,chr(235):384,chr(236):494,chr(237):494,chr(238):494,chr(239):494,chr(240):0,chr(241):329,
	chr(242):274,chr(243):686,chr(244):686,chr(245):686,chr(246):384,chr(247):384,chr(248):384,chr(249):384,chr(250):384,chr(251):384,chr(252):494,chr(253):494,chr(254):494,chr(255):0}

pdf_charwidths["times"]={chr(0):250,chr(1):250,chr(2):250,chr(3):250,chr(4):250,chr(5):250,chr(6):250,chr(7):250,chr(8):250,chr(9):250,chr(10):250,chr(11):250,chr(12):250,chr(13):250,chr(14):250,chr(15):250,chr(16):250,chr(17):250,chr(18):250,chr(19):250,chr(20):250,chr(21):250,
	chr(22):250,chr(23):250,chr(24):250,chr(25):250,chr(26):250,chr(27):250,chr(28):250,chr(29):250,chr(30):250,chr(31):250," ":250,"!":333,"\"":408,"#":500,"$":500,"%":833,"&":778,"\"":180,"(":333,")":333,"*":500,"+":564,
	",":250,"-":333,".":250,"/":278,"0":500,"1":500,"2":500,"3":500,"4":500,"5":500,"6":500,"7":500,"8":500,"9":500,":":278,";":278,"<":564,"=":564,">":564,"?":444,chr(64):921,"A":722,
	"B":667,"C":667,"D":722,"E":611,"F":556,"G":722,"H":722,"I":333,"J":389,"K":722,"L":611,"M":889,"N":722,"O":722,"P":556,"Q":722,"R":667,"S":556,"T":611,"U":722,"V":722,"W":944,
	"X":722,"Y":722,"Z":611,"[":333,"\\":278,"]":333,"^":469,"_":500,"`":333,"a":444,"b":500,"c":444,"d":500,"e":444,"f":333,"g":500,"h":500,"i":278,"j":278,"k":500,"l":278,"m":778,
	"n":500,"o":500,"p":500,"q":500,"r":333,"s":389,"t":278,"u":500,"v":500,"w":722,"x":500,"y":500,"z":444,"{":480,"|":200,"}":480,"~":541,chr(127):350,chr(128):500,chr(129):350,chr(130):333,chr(131):500,
	chr(132):444,chr(133):1000,chr(134):500,chr(135):500,chr(136):333,chr(137):1000,chr(138):556,chr(139):333,chr(140):889,chr(141):350,chr(142):611,chr(143):350,chr(144):350,chr(145):333,chr(146):333,chr(147):444,chr(148):444,chr(149):350,chr(150):500,chr(151):1000,chr(152):333,chr(153):980,
	chr(154):389,chr(155):333,chr(156):722,chr(157):350,chr(158):444,chr(159):722,chr(160):250,chr(161):333,chr(162):500,chr(163):500,chr(164):500,chr(165):500,chr(166):200,chr(167):500,chr(168):333,chr(169):760,chr(170):276,chr(171):500,chr(172):564,chr(173):333,chr(174):760,chr(175):333,
	chr(176):400,chr(177):564,chr(178):300,chr(179):300,chr(180):333,chr(181):500,chr(182):453,chr(183):250,chr(184):333,chr(185):300,chr(186):310,chr(187):500,chr(188):750,chr(189):750,chr(190):750,chr(191):444,chr(192):722,chr(193):722,chr(194):722,chr(195):722,chr(196):722,chr(197):722,
	chr(198):889,chr(199):667,chr(200):611,chr(201):611,chr(202):611,chr(203):611,chr(204):333,chr(205):333,chr(206):333,chr(207):333,chr(208):722,chr(209):722,chr(210):722,chr(211):722,chr(212):722,chr(213):722,chr(214):722,chr(215):564,chr(216):722,chr(217):722,chr(218):722,chr(219):722,
	chr(220):722,chr(221):722,chr(222):556,chr(223):500,chr(224):444,chr(225):444,chr(226):444,chr(227):444,chr(228):444,chr(229):444,chr(230):667,chr(231):444,chr(232):444,chr(233):444,chr(234):444,chr(235):444,chr(236):278,chr(237):278,chr(238):278,chr(239):278,chr(240):500,chr(241):500,
	chr(242):500,chr(243):500,chr(244):500,chr(245):500,chr(246):500,chr(247):564,chr(248):500,chr(249):500,chr(250):500,chr(251):500,chr(252):500,chr(253):500,chr(254):500,chr(255):500};

pdf_charwidths["timesB"]={chr(0):250,chr(1):250,chr(2):250,chr(3):250,chr(4):250,chr(5):250,chr(6):250,chr(7):250,chr(8):250,chr(9):250,chr(10):250,chr(11):250,chr(12):250,chr(13):250,chr(14):250,chr(15):250,chr(16):250,chr(17):250,chr(18):250,chr(19):250,chr(20):250,chr(21):250,
	chr(22):250,chr(23):250,chr(24):250,chr(25):250,chr(26):250,chr(27):250,chr(28):250,chr(29):250,chr(30):250,chr(31):250," ":250,"!":333,"\"":555,"#":500,"$":500,"%":1000,"&":833,"\"":278,"(":333,")":333,"*":500,"+":570,
	",":250,"-":333,".":250,"/":278,"0":500,"1":500,"2":500,"3":500,"4":500,"5":500,"6":500,"7":500,"8":500,"9":500,":":333,";":333,"<":570,"=":570,">":570,"?":500,chr(64):930,"A":722,
	"B":667,"C":722,"D":722,"E":667,"F":611,"G":778,"H":778,"I":389,"J":500,"K":778,"L":667,"M":944,"N":722,"O":778,"P":611,"Q":778,"R":722,"S":556,"T":667,"U":722,"V":722,"W":1000,
	"X":722,"Y":722,"Z":667,"[":333,"\\":278,"]":333,"^":581,"_":500,"`":333,"a":500,"b":556,"c":444,"d":556,"e":444,"f":333,"g":500,"h":556,"i":278,"j":333,"k":556,"l":278,"m":833,
	"n":556,"o":500,"p":556,"q":556,"r":444,"s":389,"t":333,"u":556,"v":500,"w":722,"x":500,"y":500,"z":444,"{":394,"|":220,"}":394,"~":520,chr(127):350,chr(128):500,chr(129):350,chr(130):333,chr(131):500,
	chr(132):500,chr(133):1000,chr(134):500,chr(135):500,chr(136):333,chr(137):1000,chr(138):556,chr(139):333,chr(140):1000,chr(141):350,chr(142):667,chr(143):350,chr(144):350,chr(145):333,chr(146):333,chr(147):500,chr(148):500,chr(149):350,chr(150):500,chr(151):1000,chr(152):333,chr(153):1000,
	chr(154):389,chr(155):333,chr(156):722,chr(157):350,chr(158):444,chr(159):722,chr(160):250,chr(161):333,chr(162):500,chr(163):500,chr(164):500,chr(165):500,chr(166):220,chr(167):500,chr(168):333,chr(169):747,chr(170):300,chr(171):500,chr(172):570,chr(173):333,chr(174):747,chr(175):333,
	chr(176):400,chr(177):570,chr(178):300,chr(179):300,chr(180):333,chr(181):556,chr(182):540,chr(183):250,chr(184):333,chr(185):300,chr(186):330,chr(187):500,chr(188):750,chr(189):750,chr(190):750,chr(191):500,chr(192):722,chr(193):722,chr(194):722,chr(195):722,chr(196):722,chr(197):722,
	chr(198):1000,chr(199):722,chr(200):667,chr(201):667,chr(202):667,chr(203):667,chr(204):389,chr(205):389,chr(206):389,chr(207):389,chr(208):722,chr(209):722,chr(210):778,chr(211):778,chr(212):778,chr(213):778,chr(214):778,chr(215):570,chr(216):778,chr(217):722,chr(218):722,chr(219):722,
	chr(220):722,chr(221):722,chr(222):611,chr(223):556,chr(224):500,chr(225):500,chr(226):500,chr(227):500,chr(228):500,chr(229):500,chr(230):722,chr(231):444,chr(232):444,chr(233):444,chr(234):444,chr(235):444,chr(236):278,chr(237):278,chr(238):278,chr(239):278,chr(240):500,chr(241):556,
	chr(242):500,chr(243):500,chr(244):500,chr(245):500,chr(246):500,chr(247):570,chr(248):500,chr(249):556,chr(250):556,chr(251):556,chr(252):556,chr(253):500,chr(254):556,chr(255):500}

pdf_charwidths["timesBI"]={chr(0):250,chr(1):250,chr(2):250,chr(3):250,chr(4):250,chr(5):250,chr(6):250,chr(7):250,chr(8):250,chr(9):250,chr(10):250,chr(11):250,chr(12):250,chr(13):250,chr(14):250,chr(15):250,chr(16):250,chr(17):250,chr(18):250,chr(19):250,chr(20):250,chr(21):250,
	chr(22):250,chr(23):250,chr(24):250,chr(25):250,chr(26):250,chr(27):250,chr(28):250,chr(29):250,chr(30):250,chr(31):250," ":250,"!":389,"\"":555,"#":500,"$":500,"%":833,"&":778,"\"":278,"(":333,")":333,"*":500,"+":570,
	",":250,"-":333,".":250,"/":278,"0":500,"1":500,"2":500,"3":500,"4":500,"5":500,"6":500,"7":500,"8":500,"9":500,":":333,";":333,"<":570,"=":570,">":570,"?":500,chr(64):832,"A":667,
	"B":667,"C":667,"D":722,"E":667,"F":667,"G":722,"H":778,"I":389,"J":500,"K":667,"L":611,"M":889,"N":722,"O":722,"P":611,"Q":722,"R":667,"S":556,"T":611,"U":722,"V":667,"W":889,
	"X":667,"Y":611,"Z":611,"[":333,"\\":278,"]":333,"^":570,"_":500,"`":333,"a":500,"b":500,"c":444,"d":500,"e":444,"f":333,"g":500,"h":556,"i":278,"j":278,"k":500,"l":278,"m":778,
	"n":556,"o":500,"p":500,"q":500,"r":389,"s":389,"t":278,"u":556,"v":444,"w":667,"x":500,"y":444,"z":389,"{":348,"|":220,"}":348,"~":570,chr(127):350,chr(128):500,chr(129):350,chr(130):333,chr(131):500,
	chr(132):500,chr(133):1000,chr(134):500,chr(135):500,chr(136):333,chr(137):1000,chr(138):556,chr(139):333,chr(140):944,chr(141):350,chr(142):611,chr(143):350,chr(144):350,chr(145):333,chr(146):333,chr(147):500,chr(148):500,chr(149):350,chr(150):500,chr(151):1000,chr(152):333,chr(153):1000,
	chr(154):389,chr(155):333,chr(156):722,chr(157):350,chr(158):389,chr(159):611,chr(160):250,chr(161):389,chr(162):500,chr(163):500,chr(164):500,chr(165):500,chr(166):220,chr(167):500,chr(168):333,chr(169):747,chr(170):266,chr(171):500,chr(172):606,chr(173):333,chr(174):747,chr(175):333,
	chr(176):400,chr(177):570,chr(178):300,chr(179):300,chr(180):333,chr(181):576,chr(182):500,chr(183):250,chr(184):333,chr(185):300,chr(186):300,chr(187):500,chr(188):750,chr(189):750,chr(190):750,chr(191):500,chr(192):667,chr(193):667,chr(194):667,chr(195):667,chr(196):667,chr(197):667,
	chr(198):944,chr(199):667,chr(200):667,chr(201):667,chr(202):667,chr(203):667,chr(204):389,chr(205):389,chr(206):389,chr(207):389,chr(208):722,chr(209):722,chr(210):722,chr(211):722,chr(212):722,chr(213):722,chr(214):722,chr(215):570,chr(216):722,chr(217):722,chr(218):722,chr(219):722,
	chr(220):722,chr(221):611,chr(222):611,chr(223):500,chr(224):500,chr(225):500,chr(226):500,chr(227):500,chr(228):500,chr(229):500,chr(230):722,chr(231):444,chr(232):444,chr(233):444,chr(234):444,chr(235):444,chr(236):278,chr(237):278,chr(238):278,chr(239):278,chr(240):500,chr(241):556,
	chr(242):500,chr(243):500,chr(244):500,chr(245):500,chr(246):500,chr(247):570,chr(248):500,chr(249):556,chr(250):556,chr(251):556,chr(252):556,chr(253):444,chr(254):500,chr(255):444};

pdf_charwidths["timesI"]={chr(0):250,chr(1):250,chr(2):250,chr(3):250,chr(4):250,chr(5):250,chr(6):250,chr(7):250,chr(8):250,chr(9):250,chr(10):250,chr(11):250,chr(12):250,chr(13):250,chr(14):250,chr(15):250,chr(16):250,chr(17):250,chr(18):250,chr(19):250,chr(20):250,chr(21):250,
	chr(22):250,chr(23):250,chr(24):250,chr(25):250,chr(26):250,chr(27):250,chr(28):250,chr(29):250,chr(30):250,chr(31):250," ":250,"!":333,"\"":420,"#":500,"$":500,"%":833,"&":778,"\"":214,"(":333,")":333,"*":500,"+":675,
	",":250,"-":333,".":250,"/":278,"0":500,"1":500,"2":500,"3":500,"4":500,"5":500,"6":500,"7":500,"8":500,"9":500,":":333,";":333,"<":675,"=":675,">":675,"?":500,chr(64):920,"A":611,
	"B":611,"C":667,"D":722,"E":611,"F":611,"G":722,"H":722,"I":333,"J":444,"K":667,"L":556,"M":833,"N":667,"O":722,"P":611,"Q":722,"R":611,"S":500,"T":556,"U":722,"V":611,"W":833,
	"X":611,"Y":556,"Z":556,"[":389,"\\":278,"]":389,"^":422,"_":500,"`":333,"a":500,"b":500,"c":444,"d":500,"e":444,"f":278,"g":500,"h":500,"i":278,"j":278,"k":444,"l":278,"m":722,
	"n":500,"o":500,"p":500,"q":500,"r":389,"s":389,"t":278,"u":500,"v":444,"w":667,"x":444,"y":444,"z":389,"{":400,"|":275,"}":400,"~":541,chr(127):350,chr(128):500,chr(129):350,chr(130):333,chr(131):500,
	chr(132):556,chr(133):889,chr(134):500,chr(135):500,chr(136):333,chr(137):1000,chr(138):500,chr(139):333,chr(140):944,chr(141):350,chr(142):556,chr(143):350,chr(144):350,chr(145):333,chr(146):333,chr(147):556,chr(148):556,chr(149):350,chr(150):500,chr(151):889,chr(152):333,chr(153):980,
	chr(154):389,chr(155):333,chr(156):667,chr(157):350,chr(158):389,chr(159):556,chr(160):250,chr(161):389,chr(162):500,chr(163):500,chr(164):500,chr(165):500,chr(166):275,chr(167):500,chr(168):333,chr(169):760,chr(170):276,chr(171):500,chr(172):675,chr(173):333,chr(174):760,chr(175):333,
	chr(176):400,chr(177):675,chr(178):300,chr(179):300,chr(180):333,chr(181):500,chr(182):523,chr(183):250,chr(184):333,chr(185):300,chr(186):310,chr(187):500,chr(188):750,chr(189):750,chr(190):750,chr(191):500,chr(192):611,chr(193):611,chr(194):611,chr(195):611,chr(196):611,chr(197):611,
	chr(198):889,chr(199):667,chr(200):611,chr(201):611,chr(202):611,chr(203):611,chr(204):333,chr(205):333,chr(206):333,chr(207):333,chr(208):722,chr(209):667,chr(210):722,chr(211):722,chr(212):722,chr(213):722,chr(214):722,chr(215):675,chr(216):722,chr(217):722,chr(218):722,chr(219):722,
	chr(220):722,chr(221):556,chr(222):611,chr(223):500,chr(224):500,chr(225):500,chr(226):500,chr(227):500,chr(228):500,chr(229):500,chr(230):667,chr(231):444,chr(232):444,chr(233):444,chr(234):444,chr(235):444,chr(236):278,chr(237):278,chr(238):278,chr(239):278,chr(240):500,chr(241):500,
	chr(242):500,chr(243):500,chr(244):500,chr(245):500,chr(246):500,chr(247):675,chr(248):500,chr(249):500,chr(250):500,chr(251):500,chr(252):500,chr(253):444,chr(254):500,chr(255):444}

pdf_charwidths["zapfdingbats"]={chr(0):0,chr(1):0,chr(2):0,chr(3):0,chr(4):0,chr(5):0,chr(6):0,chr(7):0,chr(8):0,chr(9):0,chr(10):0,chr(11):0,chr(12):0,chr(13):0,chr(14):0,chr(15):0,chr(16):0,chr(17):0,chr(18):0,chr(19):0,chr(20):0,chr(21):0,
	chr(22):0,chr(23):0,chr(24):0,chr(25):0,chr(26):0,chr(27):0,chr(28):0,chr(29):0,chr(30):0,chr(31):0," ":278,"!":974,"\"":961,"#":974,"$":980,"%":719,"&":789,"\"":790,"(":791,")":690,"*":960,"+":939,
	",":549,"-":855,".":911,"/":933,"0":911,"1":945,"2":974,"3":755,"4":846,"5":762,"6":761,"7":571,"8":677,"9":763,":":760,";":759,"<":754,"=":494,">":552,"?":537,chr(64):577,"A":692,
	"B":786,"C":788,"D":788,"E":790,"F":793,"G":794,"H":816,"I":823,"J":789,"K":841,"L":823,"M":833,"N":816,"O":831,"P":923,"Q":744,"R":723,"S":749,"T":790,"U":792,"V":695,"W":776,
	"X":768,"Y":792,"Z":759,"[":707,"\\":708,"]":682,"^":701,"_":826,"`":815,"a":789,"b":789,"c":707,"d":687,"e":696,"f":689,"g":786,"h":787,"i":713,"j":791,"k":785,"l":791,"m":873,
	"n":761,"o":762,"p":762,"q":759,"r":759,"s":892,"t":892,"u":788,"v":784,"w":438,"x":138,"y":277,"z":415,"{":392,"|":392,"}":668,"~":668,chr(127):0,chr(128):390,chr(129):390,chr(130):317,chr(131):317,
	chr(132):276,chr(133):276,chr(134):509,chr(135):509,chr(136):410,chr(137):410,chr(138):234,chr(139):234,chr(140):334,chr(141):334,chr(142):0,chr(143):0,chr(144):0,chr(145):0,chr(146):0,chr(147):0,chr(148):0,chr(149):0,chr(150):0,chr(151):0,chr(152):0,chr(153):0,
	chr(154):0,chr(155):0,chr(156):0,chr(157):0,chr(158):0,chr(159):0,chr(160):0,chr(161):732,chr(162):544,chr(163):544,chr(164):910,chr(165):667,chr(166):760,chr(167):760,chr(168):776,chr(169):595,chr(170):694,chr(171):626,chr(172):788,chr(173):788,chr(174):788,chr(175):788,
	chr(176):788,chr(177):788,chr(178):788,chr(179):788,chr(180):788,chr(181):788,chr(182):788,chr(183):788,chr(184):788,chr(185):788,chr(186):788,chr(187):788,chr(188):788,chr(189):788,chr(190):788,chr(191):788,chr(192):788,chr(193):788,chr(194):788,chr(195):788,chr(196):788,chr(197):788,
	chr(198):788,chr(199):788,chr(200):788,chr(201):788,chr(202):788,chr(203):788,chr(204):788,chr(205):788,chr(206):788,chr(207):788,chr(208):788,chr(209):788,chr(210):788,chr(211):788,chr(212):894,chr(213):838,chr(214):1016,chr(215):458,chr(216):748,chr(217):924,chr(218):748,chr(219):918,
	chr(220):927,chr(221):928,chr(222):928,chr(223):834,chr(224):873,chr(225):828,chr(226):924,chr(227):924,chr(228):917,chr(229):930,chr(230):931,chr(231):463,chr(232):883,chr(233):836,chr(234):836,chr(235):867,chr(236):867,chr(237):696,chr(238):696,chr(239):874,chr(240):0,chr(241):874,
	chr(242):760,chr(243):946,chr(244):771,chr(245):865,chr(246):771,chr(247):888,chr(248):967,chr(249):888,chr(250):831,chr(251):873,chr(252):927,chr(253):970,chr(254):918,chr(255):0};
            
pdf=tpdf



# ==================================================================
# PYTHON RYF ENGINE
# An engine to simplify report generation
# please see the sample to fully understand what i mean
# ==================================================================
ryftags=['papersize','ryf','ss','setfree','free','paperA4','body','pen','include','cr','ucr','imgxy','img','dn','f','fn','fs','fscale','ls',
         'link','join','lblock','to','lf','rg','lm','rm','bm','tm','fatr','clr','ps','oc','ol','oj','or','pg','def','landscape',
         'mw','mwr','rect','line','usept','undef','pop','add','mul','sub','div','tab','ptab','ctab','tc','j','ind','indw','sety']
class tdata:pass
defasz=72
def floatp(x):
  if type(x) is str:  
      if ("pt" in x):return float(x[:-2])
      if ("mm" in x):return float(x[:-2])*72/25.4
      if ("cm" in x):return float(x[:-2])*72/2.54
      if ("in" in x):return float(x[:-2])*72
  return float(x)*defasz
def coloreval(color):
    if len(color)==3:
        color=color.lower()
        hexs='0123456789abcdef'
        color=(hexs.index(color[0])*15,hexs.index(color[1])*15,hexs.index(color[2])*15)
    else:color=eval(color)
    return color    
def tokenize(txt,tags):
    n=0
    buf=[]
    txt=txt.replace('\n',' ')+' '
    while n<len(txt):
        c=txt[n]
        if c == ' ':
            n+=1
            continue
        elif c == '\\':
            a=c
            for i in range(15):
                n+=1
                if n>=len(txt):break
                c=txt[n]
                if len(a)>1 and c in " %\\_,.":
                    n-=1
                    break
                a+=c
            nn=n
            aa=a
            while a:
                ok=0
                for s in tags:
                    if a[1:]==s:
                        buf.append(a)
                        ok=1
                        break
                if ok:break
                n-=1
                a=a[0:-1]
            if not ok:
                buf.append(aa)
                n=nn
            n+=1
        elif c in '{[':
            cik=c
            if c=='{':cek='}'
            else: cek=']'
            a=''
            d=1
            while 1:
                n+=1
                if n>=len(txt):break
                c=txt[n]
                if c==cek:d-=1
                if c==cik:d+=1
                if d==0:break
                a+=c
            n+=1
            buf.append(a)
        elif c=='%':
            a=c
            while 1:
                n+=1
                if n>=len(txt):break
                c=txt[n]
                if c in " %\\,.){":break
                a+=c
            buf.append(a)
        else:
            a=c
            while 1:
                n+=1
                if n>=len(txt):break
                c=txt[n]
                if c in " %\\":break
                a+=c
            buf.append(a)
    return buf
NORMALTEXT  = 1000
NEXTLINE    = 1001
INDENT      = 1002
class RdfRender:
    def __init__(self):
        self.rndcache={}
        self.fntcache={}
        self.exhandle=[]
        self.special=[]
        self.initme(ryftags)
        self.autopage=1

        global tabulasi,tabletag
        self.addhandle(tabulasi,tabletag)

    def addhandle(self,h,tags):
        self.exhandle.append(h)
        self.initme(tags)
    def initme(self,tags):
        a=[[len(x),x] for x in tags]
        a.sort()
        a.reverse()
        self.special=self.special+[b for a,b in a]
    def loadfont(self,fn,fz):
        if (fn,fz) in self.fntcache:return self.fntcache[(fn,fz)]
        x=loadfont(fn,fz)
#        print "New font %s %s" % (fn,fz)
        self.fntcache[(fn,fz)]=x
        return x
    def dovar(self,x,canvas,base,kamus,isi,errinfo='',renderit=1,cutpage=1):
        x=self.kamus.get(x,[''])[-1]
        self.doline(x,canvas,base,kamus,isi,errinfo,renderit,cutpage)
    def cekpagecut(self,line,canvas,base,kamus,isi,errinfo='',renderit=1,cutpage=1):
        width=canvas.wPt
        height=canvas.hPt
        if renderit and cutpage and (base.posy>height-base.bm) and self.autopage:
            canvas.AddPage(base.mode)
            self.dovar('onpage',canvas,base,kamus,isi,errinfo,renderit,cutpage)
    def doline(self,line,canvas,base,kamus,isi,errinfo='',renderit=1,cutpage=1):
        try:
            global defasz,ryfcompatible
    #        print line
            if line and (line[0]=='#'):return
            tok=tokenize(line,self.special)
            if not tok:
                return
            ctr=tdata()
            ctr.c=0
            def peek(c=ctr,base=base,isi=isi,kamus=kamus,canvas=canvas):
                if c.c<len(isi[-1]):
                    x=isi[-1][c.c]
                    c.c+=1
                    if x and x[0]=='_':
                        if x=='_posy':x='%spt'%base.posy
                        elif x=='_leftm':x='%spt'%base.lm
                        elif x=='_rightm':x='%spt'%base.rm
                        elif x=='_bottomm':x='%spt'%base.bm
                        elif x=='_topm':x='%spt'%base.tm
                        elif x=='_paperw':x='%spt'%canvas.wPt
                        elif x=='_paperh':x='%spt'%canvas.hPt
                        elif x=='_widthm':x='%spt'%(canvas.wPt-base.lm-base.rm)
                        elif x=='__fontsize':
                            lo=canvas.lastFont()
                            x='%spt'%(lo[3])
                        else:
                            try:
                                x=kamus.get(x[1:],[''])[-1]
                            except:
                                print 'Error at:',errinfo
                                raise
                    return x

            isi.append(tok)
            a=base.a
            while 1: #base.cpage<=base.page:
                width=canvas.wPt
                height=canvas.hPt
                x=peek()
                if x==None:break
                if not x:pass
                elif type(x) is str and x[0]=='%':
                    self.dovar(x[1:],canvas,base,kamus,isi,errinfo,renderit,cutpage)
                elif x in ['\\body','\\paperA4']: pass
                elif x=='\\free':
                    self.autopage=0
                elif x=='\\setfree':
                    self.autopage=int(peek())
                elif x=='\\landscape':
                    base.mode='l'
                elif x=='\\papersize':
                    canvas.fwPt=floatp(peek())
                    canvas.fhPt=floatp(peek())
                elif x=='\\pg':
                    canvas.AddPage(base.mode)
                    self.dovar('onpage',canvas,base,kamus,isi,errinfo,renderit,cutpage)
                elif x=='\\ps':
                    base.posx,base.posy=floatp(peek()),floatp(peek())
                elif x=='\\join':
                    jml=int(peek())
                    k=peek()
                    x=''
                    for i in range(jml):
                        x=x+peek()
                    if k in kamus:kamus[k].append(x)
                    else: kamus[k]=[x,]
                elif x=='\\img':
                    filename=peek()
                    pos=peek().lower()
                    w=floatp(peek())
                    h=floatp(peek())
                    y=base.posy
                    wt=base.lm
                    for t in base.tab:wt+=t
                    awidth=width-wt-base.rm

                    if pos=='c':x=(awidth-w)/2+wt
                    elif pos=='l':x=wt
                    elif pos=='r':x=width-base.rm-w
                    else:x=floatp(pos)
                    w,h=canvas.Image(filename,x,y,w,h)
                    base.posy+=h
                elif x=='\\imgxy':
                    filename=peek()
                    x=floatp(peek())
                    y=floatp(peek())
                    w=floatp(peek())
                    h=floatp(peek())
                    canvas.Image(filename,x,y,w,h)
                elif x=='\\include':
                    f=file(peek())
                    isi=f.readlines()
                    f.close()
                    for l in isi:self.doline(l,canvas,base,kamus,isi)
                elif x=='\\sety':
                    base.posy=floatp(peek())
                elif x=='\\clr':
                    base.buf=[]
                elif x=='\\j':
                    base.isjoin=1
                elif x=='\\ls':
                    if ryfcompatible:base.ls=float(peek())*(1.4*canvas.lastFont()[3])
                    else:base.ls=floatp(peek())
                elif x=='\\ss':
                    base.ss=floatp(peek())
                elif x=='\\pf':
                    canvas.prevFont()
                elif x=='\\tc':
                    tc=coloreval(peek())
                    lo=canvas.lastFont()
                    canvas.setFont(lo[1],lo[2],lo[3],tc)
                elif x=='\\line':
                    x1=floatp(peek())
                    y1=floatp(peek())
                    w=floatp(peek())
                    h=floatp(peek())
                    canvas.Line(x1,y1,x1+w,y1+h)
                elif x=='\\rect':
                    x1=floatp(peek())
                    y1=floatp(peek())
                    w=floatp(peek())
                    h=floatp(peek())
                    canvas.Rect(x1,y1,w,h)
                
                elif x=='\\lblock':
                    canvas.Line(base.lm,base.posy,width-base.rm,base.posy)
                
                elif x=='\\mw':
                    base.rm=width-base.lm-floatp(peek())
                elif x=='\\mwr':
                    base.lm=width-base.rm-floatp(peek())
                elif x=='\\fatr':
                    lo=canvas.lastFont()
                    canvas.setFont(lo[1],peek(),lo[3],lo[4])
                elif x=='\\fs':
                    lo=canvas.lastFont()
                    canvas.setFont(lo[1],lo[2],floatp(peek()),lo[4])
                elif x=='\\fn':
                    lo=canvas.lastFont()
                    canvas.setFont(peek(),lo[2],lo[3],lo[4])
                elif x=='\\f':
                    fname=peek()
                    fsize=floatp(peek())
                    canvas.setFont(fname,'',fsize,(0,0,0))
                elif x=='\\pen':
                    color=coloreval(peek())
                    width=floatp(peek())
                    canvas.SetDrawColor(color[0],color[1],color[2])
                    canvas.SetLineWidth(width)
                elif x=='\\link':
                    peek()
                    peek()
                elif x=='\\usept':
                    defasz=1
                elif x=='\\ryf':
                    ryfcompatible=int(peek())
                elif x=='\\add':
                    k=peek()
                    v=peek()
                    if k in kamus:
                        kamus[k][-1]='%spt'%(floatp(kamus[k][-1])+floatp(v))
                elif x=='\\sub':
                    k=peek()
                    v=peek()
                    if k in kamus:
                        kamus[k][-1]='%spt'%(floatp(kamus[k][-1])-floatp(v))
                elif x=='\\mul':
                    k=peek()
                    v=peek()
                    if k in kamus:
                        kamus[k][-1]='%spt'%(floatp(kamus[k][-1])*floatp(v))
                elif x=='\\div':
                    k=peek()
                    v=peek()
                    if k in kamus:
                        kamus[k][-1]='%spt'%(floatp(kamus[k][-1])/floatp(v))
                elif x=='\\pg':
                    base.posy=(int(base.posy)/height+1)*height
                    if base.a:base.posy+=base.a.font[3]
                elif x=='\\pop':
                    k=peek()
                    zz=base.buf[-1].text
                    del base.buf[-1]
                    if k in kamus:kamus[k].append(zz)
                    else: kamus[k]=[zz,]
                elif x=='\\def':
                    k=peek()
                    if k in kamus:kamus[k].append(peek())
                    else: kamus[k]=[peek(),]
                elif x=='\\undef':
                    k=peek()
                    if k in kamus:
                        del kamus[k][-1]
                        if len(kamus[k])==0:del kamus[k]
                elif x in ['\\oc','\\oj','\\ol','\\or']:
    # =============================================================================================
                    def hrender(base,rend,awidth,wt,canvas,self,x):
                        if not rend:return
                        sx=0.0
                        px=wt
                        extra=0
                        mw=0
                        eat=0
                        for r in rend:
                            mw+=r[3].size[0]+r[1]
                            if r[3].tipe==INDENT or r[3].eatspace:
                                mw-=r[1]
                                eat+=1
                        mw-=r[1]
                        
                        if x=='\\oj' and len(rend)>1:
                            eat+=1
                            extra=(float(awidth)-wt-mw)/(len(rend)-eat)
                        elif x=='\\or':
                            sx=awidth-wt-mw
                        elif x=='\\oc':
                            sx=(awidth-wt-mw)/2.0
                        for r in rend:
                            if r[3].tipe==NORMALTEXT:
                                cuf=r[3].font
                                break
                        s=''
                        lr=0
                        head=0
                        hpx=sx+px
                        px=hpx
                        for r in rend:
                            if lr<0 or (r[3].tipe==NORMALTEXT and r[3].font<>cuf):
                                if s:
                                    if not head:
                                        canvas.BeginText(hpx,base.posy-base.ss,extra)
                                        head=1
                                    canvas.activateFont(cuf)
                                    if r[3].tipe==NORMALTEXT:cuf=r[3].font
                                    if r[3].eatspace:canvas.Text(s)
                                    else:canvas.Text(s+' ')
                                    px+=r[1]+extra
                                if lr<0:
                                    if not head:hpx=px
                                    else:canvas.TextXY(px,base.posy-base.ss)                                    
                                s=''
                            if r[3].tipe==NORMALTEXT:
                                if s and not r[3].eatspace:
                                    s+=' '
                                    px+=r[1]+extra
                                s =s+r[3].text
                                lr=0
                            if r[3].tipe==INDENT:
                                lr=-1
                            px=px+r[3].size[0]
                            
                        if s:
                            if not head:canvas.BeginText(hpx,base.posy-base.ss,extra)
                            canvas.activateFont(cuf)
                            canvas.Text(s)
                        canvas.EndText()
    # =============================================================================================
                    def splitword(dx,buff,old,size,self=self):
                        def vokal(x):
                            return x in 'aiueoAIUEO'
                        txt=old.text
                        wtxt=len(txt)
                        wrend=old.size[0]
                        szh=0
                        # calculate cut point
                        cut=int((size-szh)*wtxt/wrend)
                        # geser ke kiri
                        txt+='   '
                        while cut>0:
                            if not vokal(txt[cut]) and vokal(txt[cut-1]) and vokal(txt[cut+1]):break
    #                        if not vokal(txt[cut]) and vokal(txt[cut-1]):break
                            cut-=1
                        if cut<1:return
                        
                        
                        # ========
                        new=tdata()
                        new.text=old.text[cut:]
                        new.tipe=NORMALTEXT
                        new.eatspace=0
                        if new.text=='':return
                        new.font=old.font
                        old.text=old.text[:cut]
                        obr=[]
                        for ob in (old,new):
                            sz=self.canvas.TextSize(ob.text,ob.font)
                            ob.size=[sz[0],sz[1]]
                            sp1,sp2=self.canvas.TextSize(' ',ob.font)
                            obr.append([dx,sp1,0,ob])
                        old.text+='-'
                        buff.append(obr[0])
                        return obr[1]


    # ----------------------------------
                    wt=base.lm
                    for t in base.tab:wt+=t
                    awidth=width-base.rm
                    dx=wt
                    omy=base.ls
                    my=omy
                    rend=[]
                    space=0
                    spc=canvas.TextSize(' ')[0]/4
                    for b in base.buf:
                        res=None
                        if b.tipe==NORMALTEXT:fnt=b.font
                        if rend and ((dx+b.size[0]>(awidth-space) or b.tipe==NEXTLINE)):
                            if (b.tipe==NORMALTEXT and len(b.text)>3) and x=='\\oj':
                                #hyphen
                                res=splitword(dx,rend,b,awidth-space-dx)
                                my=max(my,rend[-1][-1].size[1])
                            zz=float(my-omy)
                            if zz>0:base.posy+=zz
                            if rend and renderit:
                                hrender(base,rend,awidth,wt,canvas,self,x)
                            base.posy+=float(omy)
                            self.cekpagecut(line,canvas,base,kamus,isi,errinfo,renderit,cutpage)
    #                        if renderit and cutpage and (base.posy>height-base.bm) and self.autopage:
    #                            canvas.AddPage(base.mode)
    #                            self.dovar('onpage',canvas,base,kamus,isi,errinfo,renderit,cutpage)
                            my=0
                            dx=wt
                            rend=[]
                            space=0
                            if b.tipe==NEXTLINE: continue
                        if res:
                            rend.append(res)
                            dx=dx+res[3].size[0]+res[1]
                            my=res[3].size[1]
                        else:
                            sp1=b.ssize[0]
                            rend.append([dx,sp1,0,b])
                            my=max(my,b.size[1])
                            dx=dx+b.size[0]+sp1
                    #    space=space+spc
                    if x=='\\oj':x='\\ol'
                    if rend and renderit:
                        zz=float(my-omy)
                        if zz>0:base.posy+=zz
                        hrender(base,rend,awidth,wt,canvas,self,x)
                        #base.posy+=float(omy)
                    base.buf=[]
                elif x=='\\to':
                    cuf=canvas.lastFont()
                    canvas.activateFont(cuf)
                    px=floatp(peek())
                    py=floatp(peek())
                    canvas.TextOut(px,py,peek())
                elif x=='\\cr':
                    base.posy+=base.ls
                    self.cekpagecut(line,canvas,base,kamus,isi,errinfo,renderit,cutpage)
                elif x=='\\ucr':
                    h=canvas.lastFont()[3]
                    base.posy-=base.ls
                elif x=='\\dn':
                    base.posy+=floatp(peek())
                    self.cekpagecut(line,canvas,base,kamus,isi,errinfo,renderit,cutpage)
                elif x=='\\tm':
                    base.tm=floatp(peek())
                elif x=='\\bm':
                    base.bm=floatp(peek())
                elif x=='\\lm' or x=='\\lf':
                    base.lm=floatp(peek())
                elif x=='\\rm' or x=='\\rg':
                    base.rm=floatp(peek())
                elif x=='\\tab':
                    base.tab.append(floatp(peek()))
                elif x=='\\ptab':
                    del base.tab[-1]
                elif x=='\\ctab':
                    base.tab=[]
                elif x in ['\\ind','\\indw']:
                        la=base.a
#                        if la:la.eatspace=1
                        a=tdata()
                        a.tipe=INDENT
                        a.eatspace=0
                        a.size=[0,0]
                        if x[-1]=='w':a.size[0]=floatp(peek())-la.size[0]
                        else:         a.size[0]=floatp(peek())
                        a.ssize=[0,0]
                        base.buf.append(a)
                        base.a=a
                        base.isjoin=0
                else:
                    ex=0
                    for exh in self.exhandle:
                        if exh(self,x,peek):
                            ex=1
                            break
                    # =================================================
                    if not ex:
    #                    x=str(x).strip()
                        if x:
                            if x[0:2]in ['//','/-']:
                                a=tdata()
                                a.tipe=NEXTLINE
                                a.eatspace=0
                                a.size=[0,0]
                                base.buf.append(a)
                                base.a=a
                            else:
                                if x[0]=='\\':x=x[1:]
                                if x[0]=='~':
                                    x=x[1:]
                                    base.isjoin=1
#                                if (base.isjoin) and a and a.tipe==NORMALTEXT:
#                                    a.tipe=NORMALTEXT
#                                    a.text+=str(x)
#                                    a.size=canvas.TextSize(a.text,a.font)
#                                    a.ssize=canvas.TextSize(' ',a.font)
#                                    base.a=a
#                                else:
                                a=tdata()
                                a.eatspace=base.isjoin
                                a.tipe=NORMALTEXT
                                a.font=canvas.lastFont()
                                a.text=str(x)
                                a.size=canvas.TextSize(a.text,a.font)
                                a.ssize=canvas.TextSize(' ',a.font)
                                base.buf.append(a)
                                base.a=a
                                base.isjoin=0
                    # =================================================
            del isi[-1]
        except:
            print '\nFatal Error:\n%s\n->%s' % (line,self.lineinfo)
            raise
    def do(self,isi,page,fn='filename',outp='result.pdf'):
        self.canvas=pdf()
        self.canvas.setFont('times','',12,(0,0,0))
        self.canvas.SetLineWidth(0.5)
        self.isi=[]
        base=tdata()
        self.base=base
        base.imgh=0
        base.ss=0
        base.pw=0
        base.ph=0
        base.rm=36
        base.lm=36
        base.bm=36
        base.tm=36
        base.tab=[]
        base.fsize=10
        base.fname='times'
        base.mode='p'
        base.buf=[]
        base.posx,base.posy=0,0
        self.kamus={}
        self.kamus['pagewidth']=[self.canvas.wPt,]
        self.kamus['pageheight']=[self.canvas.hPt,]
        self.kamus['onpage']=['\ps 0 2cm',]
        base.isjoin=0
        base.ls=13
        base.fsc=1.0
        base.a=0
        n=0
        ll=''
        ada=0
        ada0=0
        self.line=0
        for l in isi:
            self.line+=1
            self.lineinfo='%s-%s' % (fn,self.line)
            l=l.strip()
            n+=1
            if l and l[-1]=='\\':
                ll+=l[:-1]
                ll+=' '
            else:
                if ll:
                    l=ll+l
                    ll=''
                ada0=ada
                ada=l<>''    
                if (not ada0) and ada and ('onstartline' in self.kamus):
                    self.doline(self.kamus['onstartline'][-1],self.canvas,base,self.kamus,self.isi,'%s:%s'%(fn,n))
                if (ada0) and (not ada) and ('onemptyline' in self.kamus):
                    self.doline(self.kamus['onemptyline'][-1],self.canvas,base,self.kamus,self.isi,'%s:%s'%(fn,n))
                self.doline(l,self.canvas,base,self.kamus,self.isi,'%s:%s'%(fn,n))
        return self.canvas.Output(outp)

# ==================================================================
# PYTHON RYF TABLE ADD-ON
# An engine to create table in RYF
# please see the sample to fully understand what i mean
# ==================================================================
        
tabletag=['cellpad','newtable','tablehead','tabledata','table','itable','etable','hline','cell','cellp','tablesize','tablepos','tableresize','cl','jc']
tables=[]
cutable=None
newtable=0
class ttable:
    def __init__(self,param,ryf,intb):
        global tables
        self.param=param
        self.onh=0
        self.ryf=ryf
        self.colcount=len(param)/2
        self.cell=[]
        self.hcell=[]
        self.width=ryf.canvas.wPt-ryf.base.lm-ryf.base.rm
        self.addy=0
        self.intable=intb
        if self.intable: self.width+=tables[-1].pad*2
        self.tablesize=[self.width/self.colcount]*self.colcount        
        self.HLINE=111
        self.lastj=1
        self.pos='CENTER'
        self.new=0
        self.pad=3
    def readsize(self,peek):
        ts=[]
        for i in range(self.colcount):
            ts.append(floatp(peek()))
        self.tablesize=ts
    def resize(self,x):
        w=0
        for i in self.tablesize:w+=i
        ts=[]
        z=0
        for i in self.tablesize:
            ww=i*x/w
            z+=ww
            ts.append(ww)
        self.tablesize=ts
        self.width=z
    def addcell(self,peek):
        tcell=[]
        for i in range(self.colcount):
            v=peek()
            if v==None:v=''
            tcell.append(v)
        if self.onh:self.hcell.append(tcell)
        else:self.cell.append(tcell)
    def addhline(self):
        if self.onh:self.hcell.append(self.HLINE)
        else:self.cell.append(self.HLINE)
    def realizecell(self,cell):
        ryf=self.ryf
        celly=ryf.base.posy
        canvas=ryf.canvas
        base=ryf.base
        isi=ryf.isi
        kamus=ryf.kamus
        self.colline={}
        margin=self.pad
        self.disvline={}
        if cell==self.HLINE:
            if self.addy:base.posy-=margin/2.0
            acelly=base.posy
            ryf.canvas.Line(self.lpos,acelly,self.lpos+self.width,acelly)
            self.addy=margin
            base.posy+=self.addy
        else:
            lm=self.lpos
            rm=self.lpos
            my=0
            celly2=celly+ryf.base.ls
#            cellh=[]
#            afonts=copy.copy(canvas.afonts)
#            cbase=copy.copy(ryf.base)
            for i in range(self.colcount):
                self.colprocess=i
                ryf.base.posy=celly2-4
                rm+=self.tablesize[i]
                ryf.base.lm=lm+margin
                ryf.base.rm=ryf.canvas.wPt-rm+margin
                self.lastj=1
                j='%s \\o%s '%(cell[i],self.param[i*2+1])
                ryf.doline(j,canvas,base,kamus,isi,cutpage=0,renderit=1)
                
                my=max(my,base.posy+base.ls/10)
                lm=rm
            afonts=canvas.afonts[:]
            lm=self.lpos
            mcl=0
            for i in range(self.colcount+1):
                l=self.param[i*2]
                if l=='|':
                    if (not i in self.disvline):
                        acelly1=celly-self.addy
                        acelly2=my+margin
                        canvas.Line(lm,acelly1,lm,acelly2)
                elif l<>' ':
                    canvas.TextOut(lm,my-margin,l)
                olm=lm
                if i<self.colcount:lm+=self.tablesize[i]
                if i in self.colline:
                    mcl=max(mcl,self.colline[i])
                    acelly=my+margin
                    for j in range(self.colline[i]):
                        canvas.Line(olm,acelly,lm,acelly)
                        acelly+=margin
            base.posy=my+margin
            self.addy=0
            if self.colline.keys():
                self.addy=margin*mcl
                base.posy+=margin*mcl
            if (base.posy>canvas.hPt-base.bm) and ryf.autopage:
                acelly=base.posy
                ryf.canvas.Line(self.lpos,acelly,self.lpos+self.width,acelly)
                canvas.AddPage(base.mode)
                self.ryf.base.lm=self.olm
                self.ryf.base.rm=self.orm
                ryf.dovar('onpage',ryf.canvas,ryf.base,ryf.kamus,ryf.isi,cutpage=0)
                acelly=base.posy
                j='\\ss 0 \\f _fbody _fontsize'
                if ryfcompatible:j+=' \\ls 1'
                self.ryf.doline(j,self.ryf.canvas,self.ryf.base,self.ryf.kamus,self.ryf.isi,cutpage=0)

                if self.hcell:
                    for c in self.hcell:
                        self.realizecell(c)
                else:
                    ryf.canvas.Line(self.lpos,acelly,self.lpos+self.width,acelly)                    
    def realize(self):
        olm=self.ryf.base.lm
        orm=self.ryf.base.rm
        self.olm=olm
        self.orm=orm
        if self.intable:
            self.ryf.base.posy-=13-self.pad
            self.addy=self.pad
            self.lpos=olm-tables[-2].pad
        else:
            self.lpos=(self.ryf.canvas.wPt-olm-orm-self.width)/2+olm
        if self.pos<>-2000:
            if self.pos>=0:self.lpos=self.pos+self.olm
            else:self.lpos=(olm-orm-self.width-self.pos)+olm
        
        if not self.new:
            j='\\ss 0 \\f _fbody _fontsize'
            if ryfcompatible:j+=' \\ls 1'
            self.ryf.doline(j,self.ryf.canvas,self.ryf.base,self.ryf.kamus,self.ryf.isi,cutpage=0)
        for c in self.hcell:
            self.realizecell(c)
        for c in self.cell:
            self.realizecell(c)
        if self.intable:self.ryf.base.posy-=tables[-2].pad
        self.ryf.base.lm=self.olm
        self.ryf.base.rm=self.orm
def tabulasi(ryf,tok,peek):
    global tables,cutable,newtable
    if tok=='\\itable':
        param=peek()
        cutable=ttable(param,ryf,1)
        cutable.new=newtable
        tables.append(cutable)
        return 1
    if tok=='\\table':
        param=peek()
        cutable=ttable(param,ryf,0)
        cutable.new=newtable
        cutable.pos=-2000
        tables.append(cutable)
        return 1
    elif tok=='\\newtable':
        newtable=1
        return 1
    elif tok=='\\tablehead':
        cutable.onh=1
        return 1
    elif tok=='\\tabledata':
        cutable.onh=0
        return 1
    elif tok=='\\cellp':
        cutable.param=peek()
        cutable.addcell(peek)
        return 1
    elif tok=='\\cell':
        cutable.addcell(peek)
        return 1
    elif tok=='\\jc':
        n=int(peek())
        cutable.lastj=n
        i=cutable.colprocess+1
        for n in range(n-1):
            ryf.base.rm-=cutable.tablesize[i+n]
            cutable.disvline[i+n]=1
        return 1
    elif tok=='\\cl':
        for i in range(cutable.lastj):
            cutable.colline[cutable.colprocess+i]=cutable.colline.get(cutable.colprocess+i,0)+1
        return 1
    elif tok=='\\hline':
        cutable.addhline()
        return 1
    elif tok=='\\cellpad':
        cutable.pad=floatp(peek())
        return 1
    elif tok=='\\etable':
        cutable.realize()
        del tables[-1]
        if tables:cutable=tables[-1]
        return 1
    elif tok=='\\tablesize':
        cutable.readsize(peek)
        return 1
    elif tok=='\\tableresize':
        cutable.resize(floatp(peek()))
        return 1
    elif tok=='\\tablepos':
        cutable.pos=floatp(peek())
        return 1

# ==================================================================
# MAIN
# ==================================================================
renderer=RdfRender()
def showryf(fn='print.txt'):
    f=file(fn)
    test=f.read()
    f.close()
    f=file('result.pdf','wb')
    f.write(renderer.do(test.split('\n'),1))
    f.close()
    
showryf()
