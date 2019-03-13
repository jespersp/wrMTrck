
import ij.plugin.filter.PlugInFilter;
import java.util.*;
import java.awt.Color;
import java.awt.Frame;
import java.awt.image.IndexColorModel;
import java.awt.Font;
import java.io.*;

import ij.*;
import ij.gui.*;
import ij.io.*;
import ij.process.*;
import ij.measure.*;
import ij.text.*;
import ij.plugin.filter.ParticleAnalyzer;
import ij.plugin.filter.Analyzer;
import ij.plugin.filter.BackgroundSubtracter;
import ij.plugin.frame.Recorder;
import ij.plugin.frame.RoiManager;
import ij.macro.Interpreter;
import ij.util.Tools;
import ij.process.ImageProcessor;


/**
	wrMTrck by Jesper Søndergaard Pedersen (JSP)

	Uses ImageJ's particle analyzer to track the movement of
	multiple objects through a stack. Uses the changes in aspect
	ratio of elipse fitting to quantify "thrashing" or
	swimming motion of C. elegans worms

	Based on MTrack2 by 2003/06/28 Nico Stuurman

	History

	Build 090408
		Implemented dos.newLine() instead of hard-coded "\n"
		Changed maxAreaChange to a percentage instead of pixel value
	Build 090707
		Added summarize feature
		Added Body-bend display on showPositions
		Added posibility to make an FPS override
		Now Works with scale-calibrated images
	Build 090804
		Fixed a bug in output of raw data.
	Build 091115
		Added x-y point smoothing function to decrease the "noise" movement of immobile objects
	Build 100201
		Corrected spelling mistake in input parameter "minTrackLength" (was "minTrackLenght") - this may affect scripts.
	Build 100411
		Corrected names in some fields on the dialog
	Build 100706
		Option to output plots of thrashing analysis for quality control purposes to rapidly asses if threshold value is good
	Build 101004
		Now works on both binary and thresholded movies.
		Posibility to enable on the fly deflickering and simple background subtraction based on RB15 on first frame.
		This means that wrMTrck can now track animals in raw movies and virtual stacks.
		Hitting the ESC key aborts analysis
	Build 110617
		Added an extra input field to allow adjustment of label font size
	Build 110622
		Added output of bend-time histogram (in frames) for each animal in text file output. Switch on/off histogram by adjusting bendDetect parameter
        Build 111031
		Corrected undocumented raw data output with rawData =6
		With rawData <0 headers are suppressed.
		(Konstantine Palanski) Summary repors frames with maximum and minimum number of objects and the frame with maximum number of tracked objects
	Build 170303
		Added undocumented raw data output with rawData = 7

TODO
	(Allow user to provide a thresholded image-stack instead of requiring binary-stack) - done
	Better support for multicore CPU to speed up analysis (Not sure how much can be gained)
	Make output of histograms in more user-friendly format
	Flexible user defineable point smoothing setting instead of hard coded 5-point smoothing


*/
public class wrMTrck_ implements PlugInFilter, Measurements  {

	private	boolean           verbose = IJ.debugMode;
	ImagePlus	imp;
	int		nParticles;
	static	String 	buildNo = "Build 111031";
	static int 	fontSize = 16;
	static int	minSize = 100;
	static int	maxSize = 400;
	static float   	maxVelocity = 10;
	static float	maxAreaChange = 30;
	static int 	minTrackLength = 50;
	static float	minAngle = 2;
	static float	binSize = 0;
	static int	plotBendTrack=0;
	static boolean 	bSaveResultsFile = false;
	static boolean 	bShowLabels = true;
	static boolean 	bShowPositions = true;
	static boolean 	bShowPaths = false;
	static boolean 	bShowPathLengths = true;
	static boolean 	bShowSummary = true;
	static boolean 	bRoundCoord = false;
	static boolean  bSmoothing = true;
	static boolean  bPlotBendTrack = false;

	static int 	rawData = 0;
	static int	bendType = 2;
	static double	fps =0;
	static int	backSub = 0;
	static String	threshMode = "Otsu";
	static int 	maxColumns=75;

	//KP
	static 	int 	kpFrm = 0, kpMax = 0;
	static 	String row = new String();
	private int 	nMax =0;
	private int		nMin = 99999;
	private int		nMaxFrm=0;
	private int		nMinFrm=0;
	//EOKP

	private TextWindow tw;
	private	TextWindow tw2;
	private String 	directory,filename,rawFilename;


	private static	String prevHdr;
	private String	summaryHdr = "File\tnObj\tnObjFrm\tnFrames\tnTracks\ttotLength\tObjFrames\tObjSeconds\tavgSpeed\tavgArea\tavgPerim\tstdSpeed\tstdArea\tstdPerim"; // (KP)
	private static	String prevhHdr;
	private String	histogramHdr	= "";
	private double	pixelWidth=1.0, pixelHeight=1.0;
	private boolean suppressHeader;
	boolean done;


	public class particle {
		float	x;
		float	y;
		float	sx;		// smoothed x-coordinate
		float	sy;		// smoothed y-coordinate
		int	z;
		float	area;	// inserted by JSP
		float	major;
		float	minor;
		float	ar;
		float	angle;
		float	circularity;
		float	dist;  // contains the distance traveled since last frame.
		float   perimeter; // length of the perimeter of a object
		int	trackNr;
		boolean inTrack=false;
		boolean flag=false;

		public void copy(particle source) {
			this.x=source.x;
			this.y=source.y;
			this.z=source.z;  // frame
			this.major=source.major;
			this.minor=source.minor;
			this.ar=source.ar;
			this.area= source.area;
			this.angle = source.angle;
			this.circularity = source.circularity;
			this.dist = source.dist;
			this.perimeter = source.perimeter;
			this.inTrack=source.inTrack;
			this.flag=source.flag;
		}

		public float distance (particle p) {
			return (float) Math.sqrt(sqr(this.x-p.x) + sqr(this.y-p.y));
		}

		public float sdistance (particle p) {
			return (float) Math.sqrt(sqr(this.sx-p.sx) + sqr(this.sy-p.sy));
		}
	}

	public int setup(String arg, ImagePlus imp) {
		this.imp = imp;
		if (IJ.versionLessThan("1.17y"))
			return DONE;
		else
			return DOES_8G+NO_CHANGES;
	}
//===================================================== max
	public static double max(double[] t) {
   		double maximum = t[0];   // start with the first value
   		for (int i=1; i<t.length; i++) {
        	if (t[i] > maximum) {
            	maximum = t[i];   // new maximum
        	}
    	}
    return maximum;
}//end method max

	public void run(ImageProcessor ip) {

		AutoThresholder at = new AutoThresholder();

		GenericDialog gd = new GenericDialog("wrMTrck by Jesper S. Pedersen, "+ buildNo);
		gd.addNumericField("minSize - Minimum Object Area (pixels^2): ", minSize, 0);
		gd.addNumericField("maxSize - Maximum Object Area (pixels^2): ", maxSize, 0);
		gd.addNumericField("maxVelocity - Maximum Velocity (pixels/frame):", maxVelocity, 0);
		gd.addNumericField("maxAreaChange - Maximum area change (%):", maxAreaChange, 0);
		gd.addNumericField("minTrackLength - Minimum track length (frames):", minTrackLength, 0);
		gd.addNumericField("bendThreshold - Threshold for turn :",minAngle,1);
		gd.addNumericField("binSize - Size of bin for speed histogram (pixels/frame) (0=disable):",binSize,1);
		gd.addCheckbox("saveResultsFile - Save Results File:", bSaveResultsFile);
		gd.addCheckbox("showPathLengths - Display Path Lengths:", bShowPathLengths);
		gd.addCheckbox("showLabels - Show Labels:", bShowLabels);
		gd.addCheckbox("showPositions - Show Positions:", bShowPositions);
		gd.addCheckbox("showPaths - Show Paths:", bShowPaths);
		gd.addCheckbox("showSummary - show a summary of tracking",bShowSummary);
		gd.addCheckbox("roundCoord - round off coordinates",bRoundCoord);
		gd.addCheckbox("smoothing - point smoothing", bSmoothing);
		gd.addCheckbox("plotBendTrack - Quality control plots for thrashing analysis", bPlotBendTrack);
		gd.addNumericField("rawData - (0=off,1=XYcord,2=Ellipse,3=AreaPerimDist,4=Ellipse+Circ,5=BendCalc):", rawData, 0) ;
		gd.addNumericField("bendDetect - (0=Off,1=Angle,2=AspectRatio,3=AR+Histogram):",bendType,0);
		gd.addNumericField("FPS - frames/s (0=try to load from file):", fps,0 );
		gd.addNumericField("backSub - On-the-fly background subtraction (0=off,1=F1RB15):", backSub,0);
		gd.addChoice("threshMode - Thresholding method (only if backSub>0)",at.getMethods(), "Otsu" );
		gd.addNumericField("fontSize - Size of labeling font:", fontSize,0);
		gd.showDialog();
		if (gd.wasCanceled())
			return;
		minSize = (int)gd.getNextNumber();
		maxSize = (int)gd.getNextNumber();
		maxVelocity = (float)gd.getNextNumber();
		maxAreaChange = (float)gd.getNextNumber();
		minTrackLength = (int)gd.getNextNumber();
		minAngle = (float)gd.getNextNumber();
		binSize = (float)gd.getNextNumber();
		bSaveResultsFile = gd.getNextBoolean();
		bShowPathLengths = gd.getNextBoolean();
		bShowLabels = gd.getNextBoolean();
		bShowPositions = gd.getNextBoolean();
		bShowPaths = gd.getNextBoolean();
		bShowSummary = gd.getNextBoolean();
		bRoundCoord = gd.getNextBoolean();
		bSmoothing= gd.getNextBoolean();
		bPlotBendTrack = gd.getNextBoolean();
		rawData = (int)gd.getNextNumber();
		bendType = (int)gd.getNextNumber();
		fps= (float)gd.getNextNumber();
		backSub =(int)gd.getNextNumber();
		threshMode = gd.getNextChoice();
		fontSize = (int)gd.getNextNumber();
		if (bShowPositions)
			bShowLabels =true;

/* Extract file name of movie file opened in ImageJ */

		if (rawData <0) {suppressHeader = true ; rawData = - rawData ;}
			else {suppressHeader = false;} ;
		rawFilename= imp.getTitle();
		int dotPos = rawFilename.lastIndexOf('.');
		if (0 < dotPos && dotPos < rawFilename.length()-2) {
			rawFilename = rawFilename.substring(0,dotPos);
		}
		if (bSaveResultsFile) {
			SaveDialog sd=new  SaveDialog("Save Track Results",rawFilename,".txt");
			directory=sd.getDirectory();
			filename=sd.getFileName();
		}
    	        Frame frame = WindowManager.getFrame("Summary");

		if (done) return;

		track(imp, minSize, maxSize, maxVelocity, directory, filename);
	}


	public void track(ImagePlus imp, int minSize, int maxSize, float maxVelocity, String directory, String filename) {
		int nFrames = imp.getStackSize();
		if (nFrames<2) {
			IJ.showMessage("Tracker", "Stack required");
			return;
		}
		Calibration cal = imp.getCalibration();
		pixelWidth = cal.pixelWidth;
		pixelHeight = cal.pixelHeight;

		// Attempt to extract the frame rate for the movie if user did not provide a fps value

		if (fps<=0) {fps = cal.fps;};

		// Get information on the thresholding used

		ImageStack stack = imp.getStack();
		ImageProcessor ip = imp.getProcessor();
		double minThresh = ip.getMinThreshold();
		double maxThresh = ip.getMaxThreshold();

		if (verbose) IJ.log("min="+minThresh+",max="+maxThresh);

		// Set options for particle analyser and measurements

		int options =  (ParticleAnalyzer.EXCLUDE_EDGE_PARTICLES
                     //   |ParticleAnalyzer.INCLUDE_HOLES
                        |ParticleAnalyzer.SHOW_NONE);  // set all PA options false
		int measurements = CENTROID+AREA+ELLIPSE+PERIMETER+CIRCULARITY;

		// Initialize results table
		ResultsTable rt = new ResultsTable();
		rt.reset();

		// create storage for particle positions
		List[] theParticles = new ArrayList[nFrames];
		int trackCount=0;


		// Code required for deflickering and background subtraction on the fly
		double roiAvg[] = new double[nFrames+1];
		BackgroundSubtracter bs = new BackgroundSubtracter();

		ip = stack.getProcessor(1);
		ip.resetRoi();
		if (verbose) {
			if (ip.isBinary()) {IJ.log("The image is binary"); }
			else	{IJ.log("The image is NOT binary"); }
			}
		ImageProcessor bip = ip.crop();
		if ((backSub>0)& !ip.isBinary()) {  // subtract background if requested, but not if the image is already binary.
			bs.rollingBallBackground(bip, 15, true, true, false, false , true);
		}

		// record particle positions for each frame in an ArrayList
		IJ.showStatus("Finding all particles...");

		for (int iFrame=1; iFrame<=nFrames; iFrame++) {

			// Do frame normalization and background subtraction on the fly

			ip = stack.getProcessor(iFrame);
			if (backSub>0) {
				ImageStatistics is = ImageStatistics.getStatistics(ip, Measurements.MEAN, imp.getCalibration());
				roiAvg[iFrame]=is.mean;
				ip.resetRoi();
				ip.multiply(roiAvg[1]/roiAvg[iFrame]);
				ip.copyBits(bip,0,0,Blitter.DIFFERENCE);
				//bs.rollingBallBackground(ip, 15, false, true, false, false , true);
			}
			if (!(minThresh == -808080.0 )){ //NO_THRESHOLD )) {
				ip.setThreshold(minThresh,maxThresh,0);
				//IJ.log("preset threshold");
			} else if ((backSub>0) & !ip.isBinary()) {
				AutoThresholder at = new AutoThresholder();
				ip.setThreshold(at.getThreshold(threshMode,ip.getHistogram()),255,0);

				minThresh = ip.getMinThreshold();
				maxThresh = ip.getMaxThreshold();
				if (verbose) IJ.log("AutoThresholding with "+threshMode+": min="+minThresh+",max="+maxThresh);
			}

			theParticles[iFrame-1]=new ArrayList();
			rt.reset();
			ParticleAnalyzer pa = new ParticleAnalyzer(options, measurements, rt, minSize, maxSize);
			if (!pa.analyze(imp, ip)) return;
			float[] sxRes = rt.getColumn(ResultsTable.X_CENTROID);
			float[] syRes = rt.getColumn(ResultsTable.Y_CENTROID);
			float[] areaRes = rt.getColumn(ResultsTable.AREA);
			float[] angleRes = rt.getColumn(ResultsTable.ANGLE);
			float[] majorRes = rt.getColumn(ResultsTable.MAJOR);
			float[] minorRes = rt.getColumn(ResultsTable.MINOR);
			float[] perimRes = rt.getColumn(ResultsTable.PERIMETER);
			float[] circRes = rt.getColumn(ResultsTable.CIRCULARITY);


			if (sxRes==null) ;
				//IJ.log("Frame"+iFrame+" contains no objects!");//return;// do not exit! there may be objects on the next slice image!!!
			else {
				//IJ.log("Frame"+iFrame+" contains "+sxRes.length+" objects");
				for (int iPart=0; iPart<sxRes.length; iPart++) {
					particle aParticle = new particle();
					if (bRoundCoord) {
						aParticle.x=Math.round(sxRes[iPart]);//sxRes[iPart]; //
						aParticle.y=Math.round(syRes[iPart]);//syRes[iPart];//
					}
					else {
						aParticle.x=sxRes[iPart];
						aParticle.y=syRes[iPart];
					}

					aParticle.area=areaRes[iPart];
					aParticle.angle=angleRes[iPart];
					aParticle.major=majorRes[iPart];
					aParticle.minor=minorRes[iPart];
					if (minorRes[iPart]>0) {aParticle.ar=majorRes[iPart]/minorRes[iPart];};
					aParticle.perimeter=perimRes[iPart];
					//aParticle.circularity=circRes[iPart];
					aParticle.z=iFrame-1;
					theParticles[iFrame-1].add(aParticle);
				}
				if (sxRes.length>nMax) {
					nMax=sxRes.length; // record the maximum number of particles found in one frame.
					nMaxFrm=iFrame;  // record the frame at which the maximum number of particles is found. (KP)
				}
				if (sxRes.length<nMin) {
					nMin=sxRes.length; // record the minimum number of particles found in one frame. (KP)
					nMinFrm=iFrame;  // record the frame at which the minimum number of particles is found. (KP)
				}
			}
			IJ.showProgress((double)iFrame/nFrames);
			if (IJ.escapePressed())
				{IJ.beep(); done=true; return;}
			//IJ.log((int)iFrame+",");
		}

		// now assemble tracks out of the particle lists
		// Also record to which track a particle belongs in ArrayLists

		IJ.showStatus("Assembling tracks...");
		//IJ.log("Assembling tracks...");

		List theTracks = new ArrayList();
		for (int i=0; i<=(nFrames-1); i++) {
			IJ.showProgress((double)i/nFrames);
			if (IJ.escapePressed())
				{IJ.beep(); done=true; return;}
			if (theParticles[i].size()>0)
			  for (ListIterator j=theParticles[i].listIterator();j.hasNext();) {
				particle aParticle=(particle) j.next();
				if (!aParticle.inTrack) {
					// This must be the beginning of a new track
					List aTrack = new ArrayList();
					trackCount++;
					aParticle.inTrack=true;
					aParticle.trackNr=trackCount;
					aTrack.add(aParticle);
					// search in next frames for more particles to be added to track
					boolean searchOn=true;
					particle oldParticle=new particle();
					particle tmpParticle=new particle();
					oldParticle.copy(aParticle);
					for (int iF=i+1; iF<=(nFrames-1);iF++) {
						boolean foundOne=false;
						particle newParticle=new particle();
						for (ListIterator jF=theParticles[iF].listIterator();jF.hasNext() && searchOn;) {
							particle testParticle =(particle) jF.next();
							float distance = testParticle.distance(oldParticle);
							float areaChange = 100*Math.abs(1-testParticle.area/oldParticle.area);  // Calculate the area change in percent...

							// record a particle when it is within the search radius, and when it had not yet been claimed by another track
							if ( (distance/pixelWidth < maxVelocity) && (areaChange < maxAreaChange) && !testParticle.inTrack) {
								// if we had not found a particle before, it is easy
								if (!foundOne) {
									tmpParticle=testParticle;
									testParticle.inTrack=true;
									testParticle.trackNr=trackCount;
									testParticle.dist = distance;
									newParticle.copy(testParticle);
									foundOne=true;
								}
								else {
									// if we had one before, we'll take this one if it is closer.  In any case, flag these particles
									testParticle.flag=true;
									if (distance < newParticle.distance(oldParticle)) {
										testParticle.inTrack=true;
										testParticle.dist = distance;
										testParticle.trackNr=trackCount;
										newParticle.copy(testParticle);
										tmpParticle.inTrack=false;
										tmpParticle.trackNr=0;
										tmpParticle.dist = 0;
										tmpParticle=testParticle;
									}
									else {
										newParticle.flag=true;
									}
								}
							}
							else if (distance/pixelWidth < maxVelocity) {
							// this particle is already in another track but could have been part of this one
							// We have a number of choices here:
							// 1. Sort out to which track this particle really belongs (but how?)
							// 2. Stop this track
							// 3. Stop this track, and also delete the remainder of the other one
							// 4. Stop this track and flag this particle:
								testParticle.flag=true;
							}
						}
						if (foundOne)
							aTrack.add(newParticle);
						else
							searchOn=false;
						oldParticle.copy(newParticle);
					}
					theTracks.add(aTrack);
				}
			}
		}

		// Initiate the writing of an output textfile if a filename is given.

		boolean writefile=false;
		if (filename != null) {
			File outputfile=new File (directory,filename);
			if (!outputfile.canWrite()) {
				try {
					outputfile.createNewFile();
				}
				catch (IOException e) {
					IJ.showMessage ("Error", "Could not create "+directory+filename);
				}
			}
			if (outputfile.canWrite())
				writefile=true;
			else
				IJ.showMessage ("Error", "Could not write to " + directory + filename);
		}

		//Calculate length of paths, area of objects and number of body bends

		double[][] angles = new double[trackCount+1][nFrames];
		double[][] dAngles = new double[trackCount+1][nFrames];
		double[][] sumDAngles = new double[trackCount+1][nFrames];
		double[][] bendCounter = new double[trackCount+1][nFrames];
		double[][] dAAreas = new double[trackCount+1][nFrames];
		double[] times = new double[nFrames];
		double[][] bendTimes = new double[trackCount+1][nFrames];
		double[] rawX = new double[nFrames+2];
		double[] rawY = new double[nFrames+2];
		double[] smoothX = new double[nFrames+2];
		double[] smoothY = new double[nFrames+2];

		if (bShowPathLengths) {
			double[] lengths = new double[trackCount];
			double[] distances = new double[trackCount];
			double[] maxspeeds = new double[trackCount];
			double[] areas = new double[trackCount];
			double[] areaStdev = new double[trackCount];
			double[] perims = new double[trackCount];
			double[] perimsStdev = new double[trackCount];
			double[] bends = new double[trackCount];
			double[] avgX = new double[trackCount];
			double[] avgY = new double[trackCount];
			int[] frames = new int[trackCount];
			int[] firstFrames = new int[trackCount];
			int binNum = 0;

			if (binSize>0)
				binNum= (int) (maxVelocity/binSize+1);
			else
				binNum=100;

			/* double x1, y1, x2, y2,*/
			double distance, deltaAngle, oldAngle, sumDAngle, oldDAngle1, oldDAngle2, temp, temp2, avgArea, sumAreaSq, avgPerim, sumPerimSq, sumX, sumY, oldX, oldY;

// generate smoothed coordinates to eliminate some digital noise -
// without coordinate smoothing lenght of track for immobile particles can actually be quite long
// for now only 5-point smoothing is possible, but the number of points should be user definable in later releases

			if (bSmoothing) {

				IJ.showStatus("Smoothing tracks...");
				for (ListIterator iT=theTracks.listIterator();iT.hasNext();){
					List bTrack=(ArrayList) iT.next();
					int displayTrackNr=0;
					if (bTrack.size() >= minTrackLength) {
						displayTrackNr++;
						ListIterator jT=bTrack.listIterator();
						particle oldParticle = (particle) jT.next();
						particle oldParticle2 = oldParticle;
						rawX[1]= oldParticle.x;
						rawY[1]= oldParticle.y;
						smoothX[1]= oldParticle.x;
						smoothY[1]= oldParticle.y;
						oldParticle.sx=oldParticle.x;
						oldParticle.sy=oldParticle.y;
						int i = 1 ;
						int t = 0 ;
						for (;jT.hasNext();) {
							i++;
							particle newParticle=(particle) jT.next();
							rawX[i]= newParticle.x;
							rawY[i]= newParticle.y;
							newParticle.sx= newParticle.x;
							newParticle.sy= newParticle.y;
							smoothX[i]= newParticle.x;
							smoothY[i]= newParticle.y;
							if (i>=3) {
								temp=0;
								temp2=0;
								for (t=0;t<3;t++) {
									temp+= rawX[t+i-2];
									temp2+= rawY[t+i-2];
								}
								smoothX[i-1]=(float)temp/3;
								smoothY[i-1]=(float)temp2/3;
								oldParticle.sx=(float)temp/3;
								oldParticle.sy=(float)temp2/3;

							}
							if (i>=5) {
								temp =0;
								temp2 =0;
								for (t=0;t<5;t++) {
									temp+= rawX[t+i-4];
									temp2+= rawY[t+i-4];
								}
								smoothX[i-2]=(float)temp/5;
								smoothY[i-2]=(float)temp2/5;
								oldParticle2.sx=(float)temp/5;
								oldParticle2.sy=(float)temp2/5;

							}
							else {
							}
							oldParticle2=oldParticle;
							oldParticle=newParticle;
						}
					}
				}
			}

			int[][] bins = new int[trackCount][(int)binNum];		// used to store speed histograms
			int[][] bBins = new int[trackCount][101];				// used to store bend-histograms
			int[] FrameTrackCount = new int[nFrames];					// store how many objects are tracked in each frame


			// analyze tracks
			// Discard tracks that are smaller than minTrackLength
			// Calculate length of track
			// Calculate bends
			// Calculate how many animals are tracked on each frame


			IJ.showStatus("Analyzing tracks...");

			int trackNr=0;
			int displayTrackNr=0;
			int bendCount=0;
			int oldBendFrame=0;
			for (ListIterator iT=theTracks.listIterator(); iT.hasNext();) {
				trackNr++;
				List bTrack=(ArrayList) iT.next();
				if (bTrack.size() >= minTrackLength) {
					displayTrackNr++;
					maxspeeds[displayTrackNr-1]=0;
					ListIterator jT=bTrack.listIterator();
					particle oldParticle=(particle) jT.next();
					particle firstParticle=new particle();
					FrameTrackCount[firstParticle.z]++;
					firstParticle.copy(oldParticle);
					avgArea= oldParticle.area;
					avgPerim = oldParticle.perimeter;
					sumPerimSq= 0 ;
					sumAreaSq= 0;
					sumX=oldParticle.x;
					sumY=oldParticle.y;
					firstFrames[displayTrackNr-1]=oldParticle.z;
					oldAngle=sumDAngle=oldDAngle1=oldDAngle2=0;
					if (bendType==1) oldAngle = oldParticle.angle;
					if (bendType>1) oldAngle = oldParticle.ar;
					angles[displayTrackNr][0]=oldAngle;
					bendCount = 0;
					int i = 1 ;
					int t = 0 ;
					sumDAngle=oldDAngle1=oldDAngle2=0;
					frames[displayTrackNr-1]=bTrack.size();
					for (;jT.hasNext();) {
						i++;
						particle newParticle=(particle) jT.next();
						FrameTrackCount[newParticle.z]++;							// add one object to FrameCount at the given frame
						if (bSmoothing)	{distance= newParticle.sdistance(oldParticle);}
						else distance = newParticle.distance(oldParticle);

						// Calculate average and standard deviation of object area
						temp = (avgArea + (newParticle.area-avgArea)/i);
						sumAreaSq += (newParticle.area - avgArea)*(newParticle.area - temp);
						avgArea= temp ;

						// Calculate average and standard deviation of object perimeter
						temp = (avgPerim + (newParticle.perimeter-avgPerim)/i);
						sumPerimSq += (newParticle.perimeter - avgPerim)*(newParticle.perimeter - temp);
						avgPerim = temp;

						// Calculate the average position of the animals - e.g. useful if a single movie cointains for seprate wells
						sumX += newParticle.x;
						sumY += newParticle.y;

						if (bendType>0) {

							//detect wobbling of particle or bending of objects

							if (bendType==1) { // use the angle of the ellipse for the fitting

								deltaAngle=newParticle.angle-oldAngle;
								oldAngle=newParticle.angle;

								if (deltaAngle>100) {deltaAngle=deltaAngle-180;};	// motion probably transverse 0-180 degree boundery
								if (deltaAngle< -100) {deltaAngle=deltaAngle+180;};	// ....

							}
							else if (bendType>1) { // use the aspect ratio of the ellipse for counting body-bends
								deltaAngle=newParticle.ar - oldAngle;
								oldAngle=newParticle.ar;
								}
							else deltaAngle=0;
							angles[displayTrackNr][newParticle.z]=oldAngle;

							if (oldDAngle1*deltaAngle<=0) { 	// A change in sign indicates object started turning the other direction direction
								if (sumDAngle>minAngle) {	// if area of last turn angle was over threshold degrees then count as a bend.
			 						binNum=newParticle.z-oldBendFrame;
			 						//IJ.log("binNum:"+binNum);
			 						if (binNum<1) binNum=newParticle.z;
			 						if (binNum>100) binNum=100;
			 						bBins[displayTrackNr-1][binNum]++;
			 						dAAreas[displayTrackNr][bendCount]=sumDAngle;
			 						bendTimes[displayTrackNr][bendCount]=newParticle.z;
									bendCount++ ;
									oldBendFrame=newParticle.z;
								};
								sumDAngle=deltaAngle;		// start summing new motion
							}
							else {
								sumDAngle += deltaAngle;
							}
							bendCounter[displayTrackNr][newParticle.z]=bendCount;
							sumDAngles[displayTrackNr][newParticle.z]=sumDAngle	;

							oldDAngle1 = deltaAngle;

							dAngles[displayTrackNr][newParticle.z]=deltaAngle;
							times[newParticle.z]=newParticle.z;

						}
						// Generate a speed histogram
						if (!(newParticle.flag || oldParticle.flag)) {	// only accecpt maximum speeds for non-flagged particles
							if (binSize>0) {
								int binNr=(int)(distance/pixelWidth/binSize);
								bins[displayTrackNr-1][binNr]++;
							}
							if (distance>maxspeeds[displayTrackNr-1]) {maxspeeds[displayTrackNr-1]=distance;};
						}
						lengths[displayTrackNr-1]+=distance;
						oldParticle=newParticle;
					}
					distances[displayTrackNr-1]=oldParticle.distance(firstParticle);// Math.sqrt(sqr(oldParticle.x-firstParticle.x)+sqr(oldParticle.y-firstParticle.y));
					areas[displayTrackNr-1]=avgArea ;
					areaStdev[displayTrackNr-1] = Math.sqrt(sumAreaSq/(bTrack.size()-1)); // Calculate Stdev of the areas
					perims[displayTrackNr-1]=avgPerim;
					perimsStdev[displayTrackNr-1]= Math.sqrt(sumPerimSq/(bTrack.size()-1)); // Calculate the Stdev of the perimeters
					avgX[displayTrackNr-1]=sumX/bTrack.size();
					avgY[displayTrackNr-1]=sumY/bTrack.size();

					if (bendType ==1) bends[displayTrackNr-1]=(float)bendCount;
					else if (bendType >1) bends[displayTrackNr-1]=(float)bendCount/2;
				}
			}

//
// Generate a stack of plots, one for thrashing analysis of each track showing the raw angle or aspect ratio as well as the kpSum of the dA/dt
//

			if (bPlotBendTrack && bendType>0) {
				IJ.showStatus("Plotting bend calculation plots");

				// plot the first bend calculation for the first track
				plotBendTrack = 1;
				String YaxisLabel = "Aspect ratio";
				if (bendType==1) YaxisLabel = "Degrees";
				Plot plot = new Plot("Bend detection plot for track "+(int)plotBendTrack,"Frame#",YaxisLabel,times,sumDAngles[plotBendTrack]); //angles
				plot.setSize(nFrames+150,300);
				if (bendType>1) plot.setLimits(firstFrames[plotBendTrack-1], firstFrames[plotBendTrack-1]+frames[plotBendTrack-1], 0, Math.round(max(angles[plotBendTrack])+2));
				if (bendType==1) plot.setLimits(firstFrames[plotBendTrack-1], firstFrames[plotBendTrack-1]+frames[plotBendTrack-1], -200, 200);
				plot.setColor(Color.red);
				plot.addPoints(bendTimes[plotBendTrack],dAAreas[plotBendTrack],Plot.X);
				plot.setColor(Color.green);
				plot.addPoints(times,angles[plotBendTrack],PlotWindow.LINE); //dAngles sumDAngles
				float x1[] = {0,nFrames};
				float y1[] = {minAngle,minAngle};
				plot.setColor(Color.blue);
				plot.addPoints(x1,y1,PlotWindow.LINE);
				plot.setColor(Color.black);
				plot.draw();
				ImagePlus pimp = plot.getImagePlus();
				ImageStack plotstack = pimp.createEmptyStack();
				ImageProcessor nip = plot.getProcessor();
				plotstack.addSlice("Bend detection plot for track "+(int)plotBendTrack,nip.crop());
				ImageProcessor pip = plotstack.getProcessor(1);

				// Repeat for the rest of the plots
				for (int i=plotBendTrack;i<displayTrackNr;i++) {
					plotBendTrack++;
					IJ.showProgress((double)i/displayTrackNr);
					if (IJ.escapePressed())
						{IJ.beep(); done=true; return;}
					Plot plot2 = new Plot("Bend detection plot for track "+(int)plotBendTrack,"Frame#",YaxisLabel,times,sumDAngles[plotBendTrack]); //angles
					plot2.setSize(nFrames+150,300);
					if (bendType>1) plot2.setLimits(firstFrames[plotBendTrack-1], firstFrames[plotBendTrack-1]+frames[plotBendTrack-1], 0, Math.round(max(angles[plotBendTrack])+2));
					if (bendType==1) plot2.setLimits(firstFrames[plotBendTrack-1], firstFrames[plotBendTrack-1]+frames[plotBendTrack-1], -200, 200);
					plot2.setColor(Color.red);
					plot2.addPoints(bendTimes[plotBendTrack],dAAreas[plotBendTrack],Plot.X);
					plot2.setColor(Color.green);
					plot2.addPoints(times,angles[plotBendTrack],PlotWindow.LINE); //dAngles sumDAngles
					plot2.setColor(Color.blue);
					plot2.addPoints(x1,y1,PlotWindow.LINE);
					plot2.setColor(Color.black);
					plot2.draw();
					nip = plot2.getProcessor();
					plotstack.addSlice("Bend detection plot for track "+(int)plotBendTrack,nip.crop());
				}

				ImagePlus psimp = new ImagePlus(imp.getTitle() + " plots",plotstack);
				psimp.show();
				imp.show();
				psimp.updateAndDraw();

			}

			if (writefile) {
				try {
					File outputfile=new File (directory,filename);
					BufferedWriter dos= new BufferedWriter (new FileWriter (outputfile)); //append
					if (bendType>0){
						dos.write("Track \tLength\tDistance\t#Frames\t1stFrame\ttime(s)\tMaxSpeed\tAvgArea\tStdArea\tAvgPerim\tStdPerim\tAvgSpeed\tBLPS\tavgX\tavgX\tBends\tBBPS");
					}
					else {
						dos.write("Track \tLength\tDistance\t#Frames\t1stFrame\ttime(s)\tMaxSpeed\tAvgArea\tStdArea\tAvgPerim\tStdPerim\tAvgSpeed\tBLPS\tavgX\tavgX");
					}

					dos.newLine();
					for (int i=0; i<displayTrackNr; i++) {
						String str = "" + (i+1) + "\t" + (float)lengths[i] + "\t"
							+ (float)distances[i] + "\t"
							+ (int)frames[i]+ "\t"
							+ (int)firstFrames[i] + "\t"
							+ (float)(frames[i]/fps) +"\t"
							+ (float)fps*maxspeeds[i] + "\t"
							+ (float)areas[i]+"\t"
							+ (float)areaStdev[i]+"\t"
							+ (float)perims[i] +"\t"
							+ (float)perimsStdev[i] + "\t"
							+ (float)(fps*lengths[i]/frames[i]) + "\t"
							+ (float)(fps*2*lengths[i]/perims[i]/frames[i])+ "\t"
							+ (float)avgX[i]+ "\t"
							+ (float)avgY[i] ;

						if (bendType>0) {
								str += "\t"
							+ (float)bends[i]+ "\t"
							+ (float)fps*bends[i]/frames[i] ;
						}

						dos.write(str);
						dos.newLine();
				}
					if (binSize>0) {
						dos.newLine();
						dos.write("Bin\t");
						for (int t=0; t<displayTrackNr; t++) { dos.write("T#"+(int)(t+1)+"\t");};
						dos.newLine();

						for (int i=0; i<(int)(maxVelocity/binSize); i++) {
							String str = "" + (float)i*binSize + "\t" ;
							for (int t=0; t<displayTrackNr; t++) { str = str +bins[t][i]+"\t";};
							dos.write(str);
							dos.newLine();
						}
					}
					if(bendType>2) {
						dos.newLine();
						String str= "Bin";
						for (int t=0; t<displayTrackNr; t++) { str=str+("\tTrack"+(int)(t+1));};
						dos.write(str);
						dos.newLine();
						for (int i=0; i<101; i++) {
						    int mySum=0;
							str = "" + (float)i ;
							for (int t=0; t<displayTrackNr; t++) {
								str += "\t" +bBins[t][i];
								//mySum+=bBins[t][i];
								};
							dos.write(str);
							dos.newLine();
						}

					}
				dos.close();
				}
				catch (IOException e) {
				if (filename != null)
					IJ.error ("An error occurred writing the file. \n \n " + e);
				}

			}
			else {
					ResultsTable mrt = ResultsTable.getResultsTable();
					mrt.reset();

					for (int i=0; i<displayTrackNr; i++) {
						mrt.incrementCounter();
						mrt.addValue("Track",(i+1));
						mrt.addValue("Length",(float)lengths[i]);
						mrt.addValue("Distance",(float)distances[i]);
						mrt.addValue("#Frames",(float)frames[i]);
						mrt.addValue("1stFrame",(float)firstFrames[i]);
						mrt.addValue("Time(s)",(float)frames[i]/fps);
						mrt.addValue("MaxSpeed",(float)fps*maxspeeds[i]);
						mrt.addValue("Area",(float)areas[i]);
						mrt.addValue("sdArea",(float)areaStdev[i]);
						mrt.addValue("Perim",(float)perims[i]);
						mrt.addValue("sdPerim",(float)perimsStdev[i]);
						mrt.addValue("avgSpeed",(float)(fps*lengths[i]/frames[i]));
						mrt.addValue("BLPS",(float)(fps*2*lengths[i]/perims[i]/frames[i]));
						mrt.addValue("avgX",(float)avgX[i]);
						mrt.addValue("avgY",(float)avgY[i]);
						if(bendType>0){
							mrt.addValue("Bends",(float)bends[i]);
							mrt.addValue("BBPS",(float)fps*bends[i]/frames[i]);
						}
					}
					mrt.show("Results");

					if (binSize>0) {

						// Write histogram for individual track in the movie
						IJ.write("");
						String str = "Bin\t";
						for (int t=0; t<displayTrackNr; t++) { str=str+("Track"+(int)(t+1)+"\t");};
						str=str+"\n";
						IJ.write(str);

						for (int i=0; i<(int)(maxVelocity/binSize); i++) {
							str = "" + (float)i*binSize + "\t" ;
							for (int t=0; t<displayTrackNr; t++) { str = str +bins[t][i]+"\t";};
							IJ.write(str+"\n");

							}
					}
					// thrashing histogram
					if(bendType>2) {
						IJ.write("");
						String str= "#Frames";
						for (int t=0; t<displayTrackNr; t++) { str=str+("\tTrack"+(int)(t+1));};
						IJ.write(str+"\n");
						for (int i=0; i<101; i++) {
						    int mySum=0;
							str = "" + (float)i ;
							for (int t=0; t<displayTrackNr; t++) {
								str += "\t" +bBins[t][i];
								//mySum+=bBins[t][i];
								};
							IJ.write(str /*+(int)mySum*/ +"\n");
						}

					}

				}
			// summarize the speed histogram for the movie

			if (binSize>0) {
				histogramHdr = "Bin\t";
				String str2= rawFilename+"\t";
						for (int i=0; i<(int)(maxVelocity/binSize); i++) {
						    int mySum=0;
							histogramHdr += (float)fps*pixelWidth*i*binSize + "\t" ; //pixels/frame * µm/pixels *frame/s  pixelWidth*
							for (int t=0; t<displayTrackNr; t++) { mySum+=bins[t][i] ;}; //str = str +bins[t][i]+"\t";};
							str2+=(float) mySum + "\t";
						}

		    	        Frame frame = WindowManager.getFrame("SpeedHistogram");
    	    	    	if (frame!=null && (frame instanceof TextWindow) && histogramHdr.equals(prevhHdr))
        	    	    	tw2 = (TextWindow)frame;

        				if (tw2==null) {
            				String title = "SpeedHistogram";
							tw2 = new TextWindow(title, histogramHdr, str2, 450, 300);
							prevhHdr = histogramHdr;
        				} else
            				tw2.append(str2);
						}

/*
		//KP MAX CONCURRENT VALUES
			// Matrix that is nFrames for columns, and displayTrackNr for Rows
			int[][] kpMatrix = new int[nFrames][displayTrackNr];

			// Calculates the the lastFrame by adding each frame value to each firstFrame value
			int[] lastFrames = new int[displayTrackNr];
			for (int i=0; i < displayTrackNr; i++) {
				lastFrames[i] = firstFrames[i] + frames [i];
			}
			//Populates the kpMatrix with 1s from firstFrames[n] to lastFrames[n] one row at a time
			for(int n = 0; n < displayTrackNr; n++ ) {
				for(int i = firstFrames[n]; i < lastFrames[n]; i++) {
					kpMatrix[i][n] = 1;
				}
			}
			*/
			//Searches through kpMatrix one column at a time to find the maximum value, stores it in kpMax and kpFrm
			int kpSum;
			kpMax=0;
			for(int i = 1; i < nFrames; i++) {
				kpSum = 0;
//				for(int n = 0; n < displayTrackNr; n++) {
//					kpSum += kpMatrix[i][n];
				kpSum = FrameTrackCount[i];
//					if (n == displayTrackNr-1) {
				if (kpSum > kpMax) {
					kpMax = kpSum;
					kpFrm = i;
//						}
//					}
				}
				//IJ.log("frame,"+(int) i+ "," + (int)kpSum);
			}

			// For debugging. Outputs raw 1 and 0s to console
			// for(int i = 0; i < displayTrackNr; i++) {
				// row = "";
				// for(int n = 0; n < nFrames; n++) {
				// row = row + kpMatrix[n][i];
				// if (n == nFrames-1) {
				// System.out.println(row);
				// }
			// }
		//}
		// EOKP



			// Generate summarized output
			// filename,N,nTracks,TotLength,totFrames,TotTime,AvgSpeed,AvgArea,AvgPerim,StdSpeed,StdArea,StdPerim
			if (bShowSummary) {
				float sumLengths=0;
				float sumFrames=0;
				float sumTimes=0;
				avgArea=0;
				sumAreaSq=0;
				avgPerim=0;
				sumPerimSq=0;
				double avgSpeed=0;
				double sumSpeedSq=0;
				double speed=0;
				double sumBends=0;
				double avgBBPS=0;
				double sumBBPSSq=0;
				double BBPS=0;

				for (int i=0; i<displayTrackNr; i++) {
					sumLengths+=lengths[i];
					sumFrames+=frames[i];
					sumBends+=bends[i];

					// Calculate average and standard deviation of object area
					temp = (avgArea + (areas[i]-avgArea)/(i+1));
					sumAreaSq += (areas[i] - avgArea)*(areas[i] - temp);
					avgArea= temp ;

					// Calculate average and standard deviation of object perimeter
					temp = (avgPerim + (perims[i]-avgPerim)/(i+1));
					sumPerimSq += (perims[i] - avgPerim)*(perims[i] - temp);
					avgPerim = temp;

					// Calculate average and standard deviation of object Speed
					speed=lengths[i]/(frames[i]/fps);
					temp = (avgSpeed + (speed-avgSpeed)/(i+1));
					sumSpeedSq += (speed - avgSpeed)*(speed - temp);
					avgSpeed = temp;

					// Calculate average and standard deviation of BodyBends per seconds
					BBPS = bends[i]/(frames[i]/fps);
					temp = (avgBBPS + (BBPS-avgBBPS)/(i+1));
					sumBBPSSq += (BBPS - avgBBPS)*(BBPS - temp);
					avgBBPS = temp;

				}
		        String aLine = null;
				summaryHdr = "File\tnObjMax\tnObjMaxFrm\tnObjMin\tnObjMinFrm\tkpMax\tkpMaxFrm\tnFrames\tnTracks\ttotLength\tObjFrames\tObjSeconds\tavgSpeed\tavgArea\tavgPerim\tstdSpeed\tstdArea\tstdPerim";
				if (bendType>0) summaryHdr += "\tBends\tavgBBPS\tstdBBPS" ;

				aLine= rawFilename	+"\t"+(int)nMax 				//number of objects (N-value)
							+"\t"+(int)nMaxFrm						// frame at nMax (KP)
							+"\t"+(int)nMin							// nMin (KP)
							+"\t"+(int)nMinFrm						// frame at nMin (KP)
							+"\t"+(int)kpMax						// kpMax objects (KP)
							+"\t"+(int)kpFrm						// frame at kpMax objects (KP)
							+"\t"+(int)nFrames						// number of frames
							+"\t"+(int)displayTrackNr				//number of tracks
							+"\t"+(float)sumLengths					//total distance covered by all objects
							+"\t"+(float)sumFrames					//total number of object*frames
							+"\t"+(float)sumFrames/fps				//total obj*seconds
							+"\t"+(float)avgSpeed					//average speed (pixels/seconds)
							+"\t"+(float)avgArea					//average worm area
							+"\t"+(float)avgPerim					//average worm perimeter
							+"\t"+(float)Math.sqrt(sumSpeedSq/(displayTrackNr-1))//average speed (pixels/seconds)
							+"\t"+(float)Math.sqrt(sumAreaSq/(displayTrackNr-1))//average worm area
							+"\t"+(float)Math.sqrt(sumPerimSq/(displayTrackNr-1))	//average worm perimeter
							;
				if (bendType>0) {
					aLine +=	"\t"+(float)sumBends					// total number of body bends in the movie
							+"\t"+(float)avgBBPS					// average BBPS per track
							+"\t"+(float)Math.sqrt(sumBBPSSq/(displayTrackNr-1)) // standard deviation of BBPS per track
							;

				}

    	        //IJ.log(aLine+"\n");
    	        Frame frame = WindowManager.getFrame("Summary");
        	    if (frame!=null && (frame instanceof TextWindow) && summaryHdr.equals(prevHdr))
            	    tw = (TextWindow)frame;

        		if (tw==null) {
            		String title = "Summary";
					tw = new TextWindow(title, summaryHdr, aLine, 450, 300);
					prevHdr = summaryHdr;
        		} else
            		tw.append(aLine);

			}
		}


		// Output raw values based on user selection.
		// Create the column headings based on the number of tracks
		// with length greater than minTrackLength
		// since the number of tracks can be larger than can be accomodated by Excell, we deliver the tracks in chunks of maxColumns
		// As a side-effect, this makes the code quite complicated


		// display the table with particle positions
		// first when we only write to the screen

		String strHeadings = "Frame";
		trackCount=1;
		for (ListIterator iT=theTracks.listIterator(); iT.hasNext();) {
			List bTrack=(ArrayList) iT.next();
			if (bTrack.size() >= minTrackLength) {
				if (trackCount <= maxColumns) {
					if (rawData==1) strHeadings += "\tX" + trackCount + "\tY" + trackCount +"\tFlag" + trackCount;
					if (rawData==2) strHeadings += "\tMajor" + trackCount + "\tMinor" + trackCount + "\tAngle" + trackCount;
					if (rawData==3) strHeadings += "\tArea" + trackCount + "\tPerimeter" + trackCount + "\tDistance" + trackCount;
					if (rawData==4) strHeadings += "\tMajor" + trackCount + "\tMinor" + trackCount + "\tCircularity" + trackCount;
					if (rawData==5) strHeadings += "\tShape" + trackCount + "\tRateOfChange" + trackCount + "\tSumOfChange" + trackCount;
					if (rawData==6) strHeadings += "\tX" + trackCount + "\tY" + trackCount + "\tArea" + trackCount+"\tPerim"
						+ trackCount+"\tAngle" + trackCount+"\tAR" + trackCount+ "\tFlag" + trackCount;
					if (rawData==7) strHeadings += "\tX" + trackCount + "\tY" + trackCount + "\tMajor" + trackCount+"\tMinor" + trackCount;
				}
				trackCount++;
			}
		}
		float flag;
		String flags;
		int repeat=(int) ( (trackCount/maxColumns) );
		float reTest = (float) trackCount/ (float) maxColumns;
		if (reTest > repeat)
			repeat++;


		if (!writefile && (rawData >0)) { //bRawTracks) {
			ResultsTable rrt = new ResultsTable();
			for (int j=1; j<=repeat;j++) {
				int to=j*maxColumns;
				if (to > trackCount-1)
					to=trackCount-1;
				rrt.reset();
				String stLine="Raw Tracks " + ((j-1)*maxColumns+1) +" to " +to;
				//IJ.write(stLine);
				for(int i=0; i<=(nFrames-1); i++) {
					//String strLine = "" + (i+1);
					int trackNr=0;
					int listTrackNr=0;
					rrt.incrementCounter();
					for (ListIterator iT=theTracks.listIterator(); iT.hasNext();) {
						trackNr++;
						List bTrack=(ArrayList) iT.next();
						boolean particleFound=false;
						if (bTrack.size() >= minTrackLength) {
							listTrackNr++;
							if ( (listTrackNr>((j-1)*maxColumns)) && (listTrackNr<=(j*maxColumns))) {
								if (theParticles[i].size()>0)
								for (ListIterator k=theParticles[i].listIterator();k.hasNext() && !particleFound;) {
									particle aParticle=(particle) k.next();
									if (aParticle.trackNr==trackNr) {
										particleFound=true;
										if (aParticle.flag)
											flag=1;
										else
											flag=0;
										if (rawData==3) {
											rrt.addValue("Area"+listTrackNr,(float)aParticle.area);
											rrt.addValue("Perimeter"+listTrackNr,(float)aParticle.perimeter);
											rrt.addValue("Distance"+listTrackNr,(float)aParticle.dist);
										}
										else if (rawData==4) {
											rrt.addValue("Major"+listTrackNr,(float)aParticle.major);
											rrt.addValue("Minor"+listTrackNr,(float)aParticle.minor);
											rrt.addValue("Circularity"+listTrackNr,(float)aParticle.circularity);
										}
										else if (rawData==5) {
											rrt.addValue("Shape"+listTrackNr,(float)angles[listTrackNr][i]);
											rrt.addValue("RateOfChange"+listTrackNr,(float)dAngles[listTrackNr][i]);
											rrt.addValue("SumOfChange"+listTrackNr,(float)sumDAngles[listTrackNr][i]);
										}
										else if (rawData==6) {
											rrt.addValue("X"+listTrackNr,(float)aParticle.x);
											rrt.addValue("Y"+listTrackNr,(float)aParticle.y);
											rrt.addValue("Area"+listTrackNr,(float)aParticle.area);
											rrt.addValue("Perim"+listTrackNr,(float)aParticle.perimeter);
											rrt.addValue("Angle"+listTrackNr, (float)aParticle.angle);
											rrt.addValue("AR"+listTrackNr,(float)aParticle.ar);
											rrt.addValue("Flag"+listTrackNr,flag);//aParticle.flag);
										}
										else if (rawData==7) {
											rrt.addValue("X"+listTrackNr,(float)aParticle.x);
											rrt.addValue("Y"+listTrackNr,(float)aParticle.y);
											rrt.addValue("Major"+listTrackNr,(float)aParticle.major);
											rrt.addValue("Minor"+listTrackNr,(float)aParticle.minor);
										}
										else if (rawData==2) {
											rrt.addValue("Major"+listTrackNr,(float)aParticle.major);
											rrt.addValue("Minor"+listTrackNr,(float)aParticle.minor);
											rrt.addValue("Angle"+listTrackNr,(float)aParticle.angle);
										}
										else {
											rrt.addValue("X"+listTrackNr,(float)aParticle.x);
											rrt.addValue("Y"+listTrackNr,(float)aParticle.y);
											rrt.addValue("Flag"+listTrackNr,(int)flag);//aParticle.flag);
										}
									}
								}
							}
						}
					}
				}
				rrt.show(stLine);
			}
		}
		// and now when we write to file
		if (writefile && (rawData>0)) {
			try {

				File outputfile=new File (directory,filename.substring(0,filename.length()-4)+"_raw.txt");


//				File outputfile=new File (directory,filename);

				BufferedWriter dos= new BufferedWriter (new FileWriter (outputfile,true));
				if (!suppressHeader) {
					dos.write(strHeadings);
					dos.newLine();
					}
				for (int j=1; j<=repeat;j++) {
					int to=j*maxColumns;
					if (to > trackCount-1)
						to=trackCount-1;
					String stLine="Tracks " + ((j-1)*maxColumns+1) +" to " +to;
					if (!suppressHeader) {
						dos.write(stLine);
						dos.newLine();
					}
					for (int i=0; i<=(nFrames-1); i++) {
						String strLine = "" + (i+1);
						int trackNr=0;
						int listTrackNr=0;
						for (ListIterator iT=theTracks.listIterator(); iT.hasNext();) {
							trackNr++;
							List bTrack=(ArrayList) iT.next();
							boolean particleFound=false;
							if (bTrack.size() >= minTrackLength) {
								listTrackNr++;
								if ( (listTrackNr>((j-1)*maxColumns)) && (listTrackNr<=(j*maxColumns))) {
									for (ListIterator k=theParticles[i].listIterator();k.hasNext() && !particleFound;) {
										particle aParticle=(particle) k.next();
										if (aParticle.trackNr==trackNr) {
											particleFound=true;
											if (aParticle.flag)
												flags="*";
											else
												flags=" ";
											if (rawData==3) {
												strLine+="\t" + aParticle.area + "\t" + aParticle.perimeter + "\t" + aParticle.dist;
											}
											else if (rawData==5) {
												strLine+="\t" + angles[listTrackNr][i] + "\t" + dAngles[listTrackNr][i] + "\t" + sumDAngles[listTrackNr][i] ;
											}
											else if (rawData==6) {
												strLine+="\t" + aParticle.x + "\t" + aParticle.y + "\t" +  aParticle.area + "\t"
													+ aParticle.perimeter + "\t" + aParticle.angle+ "\t" + aParticle.ar + "\t" +  flags;
											}
											else if (rawData==7) {
												strLine+="\t" + aParticle.x + "\t" + aParticle.y + "\t" +  aParticle.major + "\t"
													+ aParticle.minor ;
											}
											else if (rawData==4) {
												strLine+="\t" + aParticle.major + "\t" + aParticle.minor + "\t" + aParticle.circularity ;
											}
											else if (rawData==2) {
												strLine+="\t" + aParticle.major + "\t" + aParticle.minor + "\t" + aParticle.angle ;
											}
											else {
												strLine+="\t" + aParticle.x + "\t" + aParticle.y + "\t" + flags;

											}
										}
									}
									if (!particleFound)
										strLine+="\t\t\t";
								}
							}
						}
						dos.write(strLine);
						dos.newLine();
					}
				}

				dos.newLine();
				dos.close();
			}
			catch (IOException e) {
				if (filename != null)
				IJ.error ("An error occurred writing the file. \n \n " + e);
			}
		}

		// Now do the fancy stuff when requested:

		// makes a new stack with objects labeled with track nr
		// optionally also displays centroid position
		IJ.showStatus("Generating movie with labels...");

		if (bShowLabels) {
			String strPart;
			ImageStack newstack = imp.createEmptyStack();
			int xHeight=newstack.getHeight();
			int yWidth=newstack.getWidth();

			for (int i=0; i<=(nFrames-1); i++) {
				if (IJ.escapePressed())
					{IJ.beep(); done=true; return;}
				int iFrame=i+1;
				String strLine = "" + i;
				ip = stack.getProcessor(iFrame);
				newstack.addSlice(stack.getSliceLabel(iFrame),ip.crop());
				ImageProcessor nip = newstack.getProcessor(iFrame);
				nip.setColor(Color.black);
//				Font f1 = Font.getFont(Font.FACE_SYSTEM, Font.STYLE_PLAIN, Font.SIZE_LARGE);
//				fontSize
				nip.setFont(new Font("SansSerif", Font.PLAIN, fontSize));
			//	nip.boldFont = true;
				// hack to only show tracks longerthan minTrackLength
				int trackNr=0;
				int displayTrackNr=0;
				for (ListIterator iT=theTracks.listIterator(); iT.hasNext();) {
					trackNr++;
					List bTrack=(ArrayList) iT.next();
					if (bTrack.size() >= minTrackLength) {
						displayTrackNr++;
						for (ListIterator k=theParticles[i].listIterator();k.hasNext();) {
							particle aParticle=(particle) k.next();
							if (aParticle.trackNr==trackNr) {
								nip.setColor(127);//Color.black);
								strPart=""+displayTrackNr;
								if (bShowPositions) {
									//if (bendType==0) strPart += "= "+(int)aParticle.x+","+(int)aParticle.y ; // bend detection not enabled plot coordinates instead
									if (bendType==1) strPart += "= b"+bendCounter[displayTrackNr][i];
									if (bendType>1) strPart += "= b"+bendCounter[displayTrackNr][i]/2;

									// we could plot a number of different infos for the particles tracked
									//{strPart+="="+/*(int)aParticle.angle+","*/+(int)aParticle.area+","+(int)aParticle.x+","+(int)aParticle.y;}
									//{strPart+="="+/*(int)aParticle.angle+","+*/(int)aParticle.area+","+bendCounter[displayTrackNr][i]/2;	};
								}
								// we could do someboundary testing here to place the labels better when we are close to the edge
								nip.moveTo((int)(aParticle.x/pixelWidth+0),doOffset((int)(aParticle.y/pixelHeight),yWidth,5) );
								//nip.moveTo(doOffset((int)aParticle.x,xHeight,5),doOffset((int)aParticle.y,yWidth,5) );
								nip.drawString(strPart);
								if (bendType==1) {
									nip.setColor(Color.gray);
									double rad = Math.toRadians(aParticle.angle+90);
									nip.moveTo((int)(aParticle.x/pixelWidth+20*Math.sin(rad)), (int)(aParticle.y/pixelHeight+20*Math.cos(rad)));
									nip.lineTo((int)(aParticle.x/pixelWidth-20*Math.sin(rad)), (int)(aParticle.y/pixelHeight-20*Math.cos(rad)));
								}
							}
						}
					}
				}
				IJ.showProgress((double)iFrame/nFrames);
			}
			ImagePlus nimp = new ImagePlus(imp.getTitle() + " labels",newstack);
			nimp.setCalibration(imp.getCalibration());
			nimp.show();
			imp.show();
			nimp.updateAndDraw();
		}


		// 'map' of tracks
		IJ.showStatus("Generating map of tracks...");
		if (bShowPaths) {
			ip = new ByteProcessor(imp.getWidth(), imp.getHeight());
			ip.setColor(Color.white);
			ip.fill();
			trackCount=0;
			int color;
			for (ListIterator iT=theTracks.listIterator();iT.hasNext();) {
				List bTrack=(ArrayList) iT.next();
				if (bTrack.size() >= minTrackLength) {
					trackCount++;
					ListIterator jT=bTrack.listIterator();
					particle oldParticle=(particle) jT.next();
					for (;jT.hasNext();) {
						particle newParticle=(particle) jT.next();
						color =Math.min(trackCount+1,254);
						ip.setValue(color);
						ip.moveTo((int)(oldParticle.x/pixelWidth), (int)(oldParticle.y/pixelHeight));
						ip.lineTo((int)(newParticle.x/pixelWidth), (int)(newParticle.y/pixelHeight));
						oldParticle=newParticle;
					}
				}
			}
			new ImagePlus("Paths", ip).show();
		}
	}



	// Utility functions
	double sqr(double n) {return n*n;}

	int doOffset (int center, int maxSize, int displacement) {
		if ((center - displacement) < 2*displacement) {
			return (center + 4*displacement);
		}
		else {
			return (center - displacement);
		}
	}

 	double s2d(String s) {
		Double d;
		try {d = new Double(s);}
		catch (NumberFormatException e) {d = null;}
		if (d!=null)
			return(d.doubleValue());
		else
			return(0.0);
	}

}


