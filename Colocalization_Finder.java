/*
 * Colocalization_Finder.java
 *
 * Created on 20/01/2005 Copyright (C) 2005 IBMP
 * ImageJ plugin
 * Version  : 1.1
 * Authors  : C. Laummonerie & J. Mutterer
 *            written for the IBMP-CNRS Strasbourg(France)
 * Email    : jerome.mutterer at ibmp-ulp.u-strasbg.fr
 * Description :  This plugin displays a correlation diagram for two 
 * images (8bits, same size). Drawing a rectangular selection 
 * on this diagram allows you to highlight corresponding pixels on a
 * RGB overlap of the original images, and if selected, on a 3rd image.
 * Analysis can be restricted to pixels having values with a minimum ratio.
 * Selection settings are logged to a results window. Large parts of this 
 * code were taken from Wayne Rasband, Pierre Bourdoncle.
 * and Gary Chinga.
 * 
 * version 1.2 : JM
 * 
 * - rewrote the mask overlay part, now faster
 * 
 * - made the scatterplot selection possible with any kind 
 *  of closed selections after several requests.
 *  
 * - the ratio bars are now overlaid on a separte layer, so that you still
 *  can read the pixel info behind these bars
 *  
 * - Fixed the Fire LUT issue (LUT was not always applied) 
 *  
 * version 1.3 : Philippe Carl
 * Email       : philippe.carl at unistra.fr
 * Date        : 4/30/2016
 * 
 * - replacement of the deprecated functions (getBoundingRect, IJ.write) by the new ones
 * 
 * - extension of the plugin for whatever picture dynamics
 * 
 * - addition of a plot (with legends, ticks (minor and major), labels) within the scatter plot
 *
 * - the selected points within the overlay picture are updated as soon as the ROI in the scatter
 *   plot is modified or dragged over
 *
 * - possibility to move the ROI position (within the scatter plot) from the mouse position
 *   within the overlay picture
 *
 * - possibility to set ROIs with given colors with a mouse double click
 *
 * - possibility to generate the x or y histogram with a Gaussian fit in order to extract
 *   the histogram maximum position by using the numeric pad 4/6 or 2/8 keys
 *  
 * version 1.4 : Philippe Carl
 * Email       : philippe.carl at unistra.fr
 * Date        : 10/20/2019
 * 
 * - Addition of scripting possibilities through plugin or macro programming
 * - The colocalization calculations are performed using double parameters instead of float
 * - Possibility to reduce the analysis to a ROI within the composite picture
 * 
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program; if not, write to the Free Software
 *   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 */
import ij.IJ;
import ij.Prefs;
import ij.ImageListener;
import ij.ImagePlus;
import ij.WindowManager;

import ij.gui.GenericDialog;
import ij.gui.ImageCanvas;
import ij.gui.ImageWindow;
import ij.gui.Overlay;
import ij.gui.Roi;
import ij.gui.RoiListener;
import ij.gui.ShapeRoi;
import ij.gui.Toolbar;

import ij.measure.CurveFitter;

import ij.plugin.Colors;
import ij.plugin.PlugIn;
import ij.plugin.RGBStackMerge;
import ij.plugin.filter.ThresholdToSelection;
import ij.plugin.frame.Fitter;
import ij.plugin.frame.RoiManager;

import ij.process.ByteProcessor;
import ij.process.ImageConverter;
import ij.process.ImageProcessor;
import ij.process.ImageStatistics;
import ij.process.ShortProcessor;

import ij.text.TextWindow;

import ij.util.ArrayUtil;
import ij.util.Tools;

import java.awt.Color;
import java.awt.FontMetrics;
import java.awt.Rectangle;
import java.awt.Toolkit;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.WindowListener;
import java.awt.event.WindowEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.Point;

import java.util.Arrays;

import javax.swing.Timer;

public class Colocalization_Finder	implements	PlugIn, WindowListener, ImageListener, RoiListener, KeyListener, MouseListener, MouseMotionListener, Runnable
{
	private static int 				multiClickInterval;
	private Thread					bgThread;		// thread for launching the calculation (in the background)
			Toolkit					toolkit;
			Integer					interval;
			Timer					timer;
			ImageCanvas				canvas, canvasResu, ccr, cc3, icc;
			ImageConverter			image1Converter , image2Converter;
			ImagePlus				image1          , image2         ,                         imp;
			ImageWindow			   	                               scatterPlotWindow;
			ImageStatistics			image1Statistics, image2Statistics;
			boolean					previousblackBackgroundState;
			boolean					mouseInsideResultImage	= false;
			boolean					mouseInsideScatterPlot	= false;
			boolean					scatterPlotModified		= true;
			boolean					resultImageModified		= true;
			int					[]	wList;
			String					str;
			String				[]	titles;
	static	Colocalization_Finder	instance;
	static	ImagePlus			   		                               scatterPlot        				    , resultImage;
	static	ImageProcessor			image1Processor , image2Processor, scatterPlotProcessor;
	static	ImageProcessor			mask, colocMask;
	static	ThresholdToSelection	ts;
	static	Overlay													   scatterplotOverlay    				, resultImageOverlay;
	static	CurveFitter				cf;
	static	TextWindow				ResultsWindow;
	static	     Roi				colocMaskRoi,                      scatterPlotRoi						, resultImageRoi;
	static	ShapeRoi				sr1, sr2;
	static	RoiManager				rm;
	static	Rectangle				coord, rect;
	static	String					title        = "Colocalization_Finder";
	static	String					ResultsTitle = "Colocalization Finder Results";
	static	String					ResultsHeadings;
	static	boolean					pearson = true;
	static	boolean					resultsWindowCreated   = false;
	static	boolean					doubleClick;
	static	int						i, npixels, clickCount, counter, i1Index, i2Index, i3Index, x, y, z1, z2, count;
	static	int						windowOffset, xOffset, yOffset, w1, w2, h1, h2, roiWidth, roiHeight;
	static	int						vi1, vi2, pos, color, minI1, maxI1, maxI2, minI2;
	static	double					val, percentPixels, min1, max1, min2, max2;
	static	byte				[]	maskPixels;
	static	double				[]	lesx, lesy, cfParams;
	static	Point				[]	pointsInsideRoi;
	static	ColorDefinition		[]	colors;

	public Colocalization_Finder()
	{
		toolkit						=			Toolkit.getDefaultToolkit();
		interval					= (Integer) toolkit.getDesktopProperty("awt.multiClickInterval");
		if (interval == null)
			multiClickInterval		= 200;
		else
			multiClickInterval		= interval.intValue();
	}

	public void run(String arg)
	{
		if (IJ.versionLessThan("1.52r"))
			return;
		IJ.register						(Colocalization_Finder.class);
		previousblackBackgroundState	= Prefs.blackBackground;
		Prefs.blackBackground			= false;
		instance						= this;

		wList = WindowManager.getIDList();
		if (wList == null || wList.length < 2)
		{
			IJ.showMessage(title, "There must be at least two windows open");
			return;
		}

		titles = new String[wList.length];
		for (i = 0; i < wList.length; i++)
		{
			imp = WindowManager.getImage(wList[i]);
			if (imp != null)
				titles[i] = imp.getTitle();
			else
				titles[i] = "";
		}

		if (!showDialog())
			return;

		ResultsHeadings = "Pearson's_Rr\tOverlap_R\tk1\tk2\tSlope\tIntercept\tnb_pixels\t%pixels\tmin_I1\tmax_I1\tmin_I2\tmax_I2\t<" + titles[i1Index] + ">\t<" + titles[i2Index] + ">\tROI_color";
		defineColors();

		build_scatter_plot();
		IJ.run(scatterPlot, "Fire", "");
		IJ.run(scatterPlot, "Enhance Contrast", "saturated=0.5");

//		resultImage.show();
		resultsWindowCreated = false;
		comparison(false, false);
	}
	
	public void run()
	{
		while (true)
		{
//			IJ.wait(50);								// delay to make sure the roi has been updated
			if (scatterPlotModified)
			{
				comparison(false, false);
				scatterPlot.draw();
			}
			else if (resultImageModified)
			{
				rebuild_scatter_plot();
				comparison(false, false);
			}
			synchronized (this)
			{
				if (scatterPlotModified)
				{
					scatterPlotModified = false;		// and loop again
				}
				else if (resultImageModified)
				{
					resultImageModified = false;		// and loop again
				}
				else
				{
					try
					{
						wait();							// notify wakes up the thread
					}
					catch(InterruptedException e)
					{
						return;							// interrupted tells the thread to exit
					}
				}
			}
		}
	}

	public boolean showDialog()
	{
		GenericDialog gd		= new GenericDialog(title);
		gd.addChoice			("Image_1 (will be shown in red):     "               , titles, titles[0]);
		gd.addChoice			("Image_2 (will be shown in green):"                  , titles, titles[1]);

		gd.showDialog();
		if (gd.wasCanceled())
			return false;
		i1Index					= gd.getNextChoiceIndex();
		i2Index					= gd.getNextChoiceIndex();
		image1					= WindowManager.getImage(wList[i1Index]).duplicate();
		image2					= WindowManager.getImage(wList[i2Index]).duplicate();
		
		w1						= image1.getWidth();
		w2						= image2.getWidth();
		h1						= image1.getHeight();
		h2						= image2.getHeight();

		if (w1 != w2 || h1 != h2)
		{
			IJ.showMessage(title, "Images 1 and 2 must be at the same height and width");
			return false;
		}

		image1Statistics		= image1.getStatistics();
		image2Statistics		= image2.getStatistics();
		min1					= image1Statistics.min;
		max1					= image1Statistics.max;
		min2					= image2Statistics.min;
		max2					= image2Statistics.max;

		// create the overlay and mask image.
		ImagePlus[] images		= { image1, image2 };
		resultImage				= RGBStackMerge.mergeChannels		(images, true);
		resultImage				.show();
		resultImage				.getCanvas().addMouseListener		(this);
		resultImage				.getCanvas().addMouseMotionListener	(this);

		maskPixels				= new byte[w1 * h1];
		Arrays					.fill(maskPixels, (byte) 0);

		windowOffset = 80;
//		scatterPlot = new ImagePlus("ScatterPlot", new ShortProcessor(256 + windowOffset, 256 + windowOffset));
		scatterPlot = new ImagePlus("ScatterPlot", new ByteProcessor (256 + windowOffset, 256 + windowOffset));
		scatterPlot.addImageListener(this);

		scatterPlot			.show();
		scatterPlotWindow	= scatterPlot.getWindow				();
		scatterPlotWindow	.addKeyListener     	    		(this);
		canvas				= scatterPlotWindow.getCanvas		();
		canvas				.addKeyListener						(this);
		canvas				.addMouseListener					(this);
		
		return true;
	}

	public void build_scatter_plot()
	{
		xOffset					= 60;
		yOffset					= windowOffset - xOffset;
		image1Processor			= image1.getProcessor();
		image2Processor			= image2.getProcessor();
		scatterPlotProcessor	= scatterPlot.getProcessor();
		for (y = 0; y < h1; y++)
		{
			for (x = 0; x < w1; x++)
			{
				z1				=       (int) (image1Processor     .getPixelValue(x, y) * 256 / max1);
				z2				= 256 - (int) (image2Processor     .getPixelValue(x, y) * 256 / max2);
				count			=       (int) scatterPlotProcessor.getPixelValue(z1 + xOffset, z2 + yOffset);
				count++;
				scatterPlotProcessor.putPixelValue(z1 + xOffset, z2 + yOffset, count);
			}
		}
//		scatterPlot				.setRoi(new Roi(xOffset + 256 + 1 - 150, yOffset, 150, 150));
		scatterPlot				.setRoi(new Roi(xOffset, yOffset, 257, 257));
//		scatterPlot				.setRoi(new Roi(xOffset + 20, yOffset, 237, 237));
		scatterPlotRoi			= scatterPlot.getRoi();
		scatterPlotRoi			.addRoiListener(this);
//		resultImageRoi			= resultImage.getRoi();
//		resultImageRoi			.addRoiListener(this);
		
		build_plot_for_scatter_plot();
	}

	static public void rebuild_scatter_plot()
	{
		for (y = 0; y <= 256; y++)
			for (x = 0; x <= 256; x++)
				scatterPlotProcessor.putPixelValue(x + xOffset, y + yOffset, 0);

		resultImageRoi			= resultImage.getRoi();
		if (resultImageRoi != null)
		{
			rect				= resultImageRoi.getBounds();
			if (rect.width == 0 || rect.height == 0)
				resultImageRoi = null;
		}

		if(resultImageRoi == null)
		{	// There is no ROI within the result image, thus I make the analysis within the whole picture
			for (y = 0; y < h1; y++)
			{
				for (x = 0; x < w1; x++)
				{
					z1				=       (int) (image1Processor     .getPixelValue(x, y) * 256 / max1);
					z2				= 256 - (int) (image2Processor     .getPixelValue(x, y) * 256 / max2);
					count			=       (int) scatterPlotProcessor.getPixelValue(z1 + xOffset, z2 + yOffset);
					count++;
					scatterPlotProcessor.putPixelValue(z1 + xOffset, z2 + yOffset, count);
				}
			}
		}
		else
		{	// There a no ROI within the result image, thus I make the analysis only within the ROI elements
			pointsInsideRoi = resultImageRoi.getContainedPoints();

			for (i = 0; i != pointsInsideRoi.length; i++)
			{
				if(pointsInsideRoi[i].x >= 0 && pointsInsideRoi[i].x < w1 && pointsInsideRoi[i].y >= 0 && pointsInsideRoi[i].y < h1)
				{
					z1				=       (int) (image1Processor     .getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) * 256 / max1);
					z2				= 256 - (int) (image2Processor     .getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) * 256 / max1);
					count			=       (int) scatterPlotProcessor.getPixelValue(z1 + xOffset, z2 + yOffset);
					count++;
					scatterPlotProcessor.putPixelValue(z1 + xOffset, z2 + yOffset, count);
				}
			}
		}
		scatterPlot.updateAndDraw();
	}

	public static String analyze(boolean _write_results, boolean _set_roi, String separator)
	{
		rebuild_scatter_plot();
		comparison(_write_results, _set_roi);

		if (_set_roi)
			return getResultsAsString(separator) + ";" + colors[color].name;
		else
			return getResultsAsString(separator);
	}

	public static String analyze(boolean _write_results, boolean _set_roi)
	{
		return analyze(_write_results, _set_roi, ";");
	}
	
	public static String analyze(boolean _write_results, boolean _set_roi, int[] _outputIDs, String separator)
	{
		int 		i;
		String 		output;
		String	[]	outputs;
		
		rebuild_scatter_plot();
		comparison(_write_results, _set_roi);

		if (_set_roi)
			output = getResultsAsString(";") + ";" + colors[color].name;
		else
			output = getResultsAsString(";");

		Arrays.sort(_outputIDs);
		outputs	= Tools.split(output, ";");
		output	= _outputIDs[0] < outputs.length ? outputs[_outputIDs[0]] : "outOfBoundsOfChosenIndex";
		for(i = 1; i != _outputIDs.length; i++)
			if(_outputIDs[i] < outputs.length)
				output += separator + outputs[_outputIDs[i]];
			else
				output += separator + "outOfBoundsOfChosenIndex";

		return output;
	}

	public static String analyze(boolean _write_results, boolean _set_roi, int[] _outputIDs)
	{
		return analyze(_write_results, _set_roi, _outputIDs, ";");
	}
	
	// call("Colocalization_Finder.analyzeByMacro", _write_results, _set_roi);
	public static String analyzeByMacro(String _write_results, String _set_roi)
	{
		return analyze(Boolean.valueOf(_write_results), Boolean.valueOf(_set_roi));
	}

	public static String analyzeByMacro(String _write_results, String _set_roi, String _outputIDs, String separator)
	{
		int			i, j;
		int		[]	outputIDs		, outputIDsSub;
		String	[]	outputIDSplitted, outputIDSplittedSub, outputIDSplittedFull;
		
		outputIDSplitted	= Tools.split(_outputIDs, ",");
		for(i = 0; i != outputIDSplitted.length; i++)
		{
			if(outputIDSplitted[i].indexOf("-") != -1)
			{
				outputIDSplittedSub		= Tools.split(outputIDSplitted[i], "-");
				outputIDsSub			= new int[2];
				outputIDsSub[0]			= Integer.valueOf(outputIDSplittedSub[0]);
				outputIDsSub[1]			= Integer.valueOf(outputIDSplittedSub[1]);
				Arrays.sort				(outputIDsSub);
				for(j = i; j != outputIDSplitted.length - 1; j++)
					outputIDSplitted[j] = outputIDSplitted[j + 1];
				outputIDSplitted[outputIDSplitted.length - 1] = String.valueOf(outputIDsSub[0]);
				outputIDSplittedSub		= new String[outputIDsSub[1] - outputIDsSub[0]];
				for(j = 0; j != outputIDSplittedSub.length; j++)
					outputIDSplittedSub[j] = String.valueOf(outputIDsSub[0] + 1 + j);
				outputIDSplittedFull	= Arrays.copyOf(outputIDSplitted, outputIDSplitted.length + outputIDSplittedSub.length);
				System.arraycopy		(outputIDSplittedSub, 0, outputIDSplittedFull, outputIDSplitted.length, outputIDSplittedSub.length);
				outputIDSplitted		= outputIDSplittedFull;
				i--;
			}
		}
		outputIDs			= new int[outputIDSplitted.length];
		for(i = 0; i != outputIDSplitted.length; i++)
			outputIDs[i] = Integer.valueOf(outputIDSplitted[i]);

		return analyze(Boolean.valueOf(_write_results), Boolean.valueOf(_set_roi), outputIDs, separator);
	}

	public static String analyzeByMacro(String _write_results, String _set_roi, String _outputIDs)
	{
		return analyzeByMacro(_write_results, _set_roi, _outputIDs, ";");
	}

	static void comparison(boolean write_results, boolean set_roi)
	{
		scatterPlotRoi			=		scatterPlot		.getRoi();

		if(scatterPlotRoi == null)
		{
			scatterPlotRoi =  new Roi(xOffset, yOffset, 257, 257);
//			scatterPlotRoi =  new Roi(xOffset + 20, yOffset, 237, 237);
			scatterPlot.setRoi(scatterPlotRoi);
		}
		else
		{
			rect				=		scatterPlotRoi	.getBounds();
			if (rect.width == 0 || rect.height == 0)
			{
				scatterPlotRoi =  new Roi(xOffset, yOffset, 257, 257);
//				scatterPlotRoi =  new Roi(xOffset + 20, yOffset, 237, 237);
				scatterPlot.setRoi(scatterPlotRoi);
			}
		}

		coord					=		scatterPlotRoi	.getBounds();
		minI1					=       coord.x - xOffset;
		maxI1					=       coord.x - xOffset + coord.width - 1;
		minI2					= 257 - coord.y + yOffset - coord.height;
		maxI2					= 256 - coord.y + yOffset;

		counter					= 0;

		resultImageRoi	= resultImage.getRoi();
		if(resultImageRoi != null)
		{
			rect				= resultImageRoi.getBounds();
			if (rect.width == 0 || rect.height == 0)
				resultImageRoi = null;
		}

		if(resultImageRoi == null)
		{	// There is no ROI within the result image, thus I make the analysis within the whole picture
			lesx = new double[w1 * h1];
			lesy = new double[w1 * h1];
			
			for (y = 0; y < h1; y++)
			{
				for (x = 0; x < w1; x++)
				{
					pos = y * w1 + x;
					vi1 = (int) (image1Processor.getPixelValue(x, y) * 256 / max1);
					vi2 = (int) (image2Processor.getPixelValue(x, y) * 256 / max2);
					setMaskPixels();
				}
			}
		}
		else
		{	// There is a ROI within the result image, thus I make the analysis only within the ROI elements
			pointsInsideRoi = resultImageRoi.getContainedPoints();
			lesx = new double[pointsInsideRoi.length];
			lesy = new double[pointsInsideRoi.length];

			for (i = 0; i != pointsInsideRoi.length; i++)
			{
				if(pointsInsideRoi[i].x >= 0 && pointsInsideRoi[i].x < w1 && pointsInsideRoi[i].y >= 0 && pointsInsideRoi[i].y < h1)
				{
					pos = pointsInsideRoi[i].y * w1 + pointsInsideRoi[i].x;
					vi1 = (int) (image1Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) * 256 / max1);
					vi2 = (int) (image2Processor.getPixelValue(pointsInsideRoi[i].x, pointsInsideRoi[i].y) * 256 / max2);
					setMaskPixels();
				}
			}
		}

		colocMask				= new ByteProcessor(w1, h1, maskPixels);
		colocMask				.setBinaryThreshold();
		ts						= new ThresholdToSelection();
		colocMaskRoi			= ts.convert(colocMask);

		if (resultImageRoi		!= null)
		{
			if (resultImageRoi instanceof ShapeRoi)
				sr1				= (ShapeRoi)resultImageRoi.clone();
			else
				sr1				= new ShapeRoi(resultImageRoi);

			if (colocMaskRoi instanceof ShapeRoi)
				sr2				= (ShapeRoi)colocMaskRoi.clone();
			else
				sr2				= new ShapeRoi(colocMaskRoi);

			colocMaskRoi		= sr1.and(sr2);
		}
		colocMaskRoi			.setFillColor(Colors.decode("#EEFFFFFF", null));
//		resultImage				.setRoi(colocMaskRoi);
		resultImageOverlay		= resultImage.getOverlay();
		if (resultImageOverlay	== null)
		{
			resultImageOverlay	= new Overlay();	
			resultImageOverlay	.addElement(colocMaskRoi);
		}
		else
			resultImageOverlay	.set(colocMaskRoi, resultImageOverlay.size() - 1);
		resultImage				.setOverlay(resultImageOverlay);

//		if (set_roi && IJ.getToolName() != "polygon")
//		if (set_roi && (IJ.getToolName() == "rectangle" || IJ.getToolName() == "roundrect" || IJ.getToolName() == "rotrect" || IJ.getToolName() == "oval" || IJ.getToolName() == "ellipse" || IJ.getToolName() == "brush" || IJ.getToolName() == "freehand" || IJ.getToolName() == "polygon"))
		if (set_roi && Toolbar.getInstance().getToolId() < 4)
		{
			scatterPlotRoi		= scatterPlot.getRoi();
			color				= color < 4 ? color + 1 : 0;
			scatterPlotRoi		.setStrokeColor(colors[color].color);
			rm					= RoiManager.getInstance();
			if (rm == null) rm	= new RoiManager();
			rm					.addRoi(scatterPlotRoi);
			rm					.rename(rm.getCount() - 1, colors[color].name);
			rm					.runCommand(scatterPlot, "Show All without labels");
			rm					.runCommand(resultImage, "Show None");	// Line added to get rid of the Rois within the RoiManager which are added by the line "rm.runCommand(i3,"Show All without labels");" in the case imResu is the selected window - And I don't know why!!!
			scatterPlot			.restoreRoi();
			scatterPlotRoi		= scatterPlot.getRoi();
			scatterPlotRoi		.setStrokeColor(Color.yellow);

			resultImageOverlay	= resultImage.getOverlay();
//			if (resultImageOverlay == null) resultImageOverlay = new Overlay();	
			colocMaskRoi		.setFillColor(colors[color].color);
//			resultImage			.setRoi(colocMaskRoi);
			resultImageOverlay	.addElement(colocMaskRoi);
			resultImage			.setOverlay(resultImageOverlay);
//			resultImage			.killRoi();
		}

		percentPixels = ((double) counter / (w1 * h1)) * 100.0;

		cf = new CurveFitter(lesx, lesy);
		cf.doFit(CurveFitter.STRAIGHT_LINE);
		cfParams = cf.getParams();

//		if (write_results && IJ.getToolName() != "polygon")
//		if (write_results && (IJ.getToolName() == "rectangle" || IJ.getToolName() == "roundrect" || IJ.getToolName() == "rotrect" || IJ.getToolName() == "oval" || IJ.getToolName() == "ellipse" || IJ.getToolName() == "brush" || IJ.getToolName() == "freehand" || IJ.getToolName() == "polygon"))
		if (write_results && Toolbar.getInstance().getToolId() < 4)
		{
			if (!resultsWindowCreated)
			{
				ResultsWindow        = new TextWindow(ResultsTitle, ResultsHeadings, "", 1040, 300);
				ResultsWindow        .addWindowListener(instance);
				resultsWindowCreated = true;
			}
			if (set_roi)
				ResultsWindow.append( getResultsAsString("\t") + "\t" + colors[color].name );
			else
				ResultsWindow.append( getResultsAsString("\t") );
		}
	}

	static void setMaskPixels()
	{
		if (scatterPlotRoi.contains(vi1 + xOffset, 256 - vi2 + yOffset))
		{
			maskPixels	[pos]		= (byte) 0;
			lesx		[counter]	= vi1;
			lesy		[counter]	= vi2;
			counter++;
		}
		else
			maskPixels	[pos]		= (byte) 255;
	}

	static double getOverlap(double[] d1, double[] d2)
	{
		double t1;
		double t2;
		double  sum		= 0.d;
		double ssum1	= 0.d;
		double ssum2	= 0.d;

		for (int i = 0; i < d1.length; i++)
		{
			t1 = d1[i];
			t2 = d2[i];
			sum = sum + (t1 * t2);
			ssum1 = ssum1 + (t1 * t1);
			ssum2 = ssum2 + (t2 * t2);
		}
		double r = sum / ((double) Math.sqrt(ssum1 * ssum2));
		return (r);
	}

	static double getContrib(double[] d1, double[] d2)
	{
		double t1;
		double t2;
		double  sum		= 0.d;
		double ssum1	= 0.d;

		for (int i = 0; i < d1.length; i++)
		{
			t1 = d1[i];
			t2 = d2[i];
			sum = sum + (t1 * t2);
			ssum1 = ssum1 + (t1 * t1);
		}
		return sum / ((double) ssum1);
	}

	/* methods from G.Chinga */

	static double getR(double[] d1, double[] d2)
	{
		double t1;
		double t2;
		double sum		= 0.d;
		double xMean	= getMean	(d1);
		double yMean	= getMean	(d2);
		double xStd		= getStd	(xMean, d1);
		double yStd		= getStd	(yMean, d2);

		for (int i = 0; i < d1.length; i++)
		{
			t1 = (d1[i] - xMean) / xStd;
			t2 = (d2[i] - yMean) / yStd;
			sum = sum + (t1 * t2);
		}

		return sum / (d1.length - 1);
	}

	static double sqr(double x)
	{
		return x * x;
	}

	static double getMean(double[] dataset)
	{
		double mValue = 0.d;

		for (int j = 0; j < dataset.length; j++)
			mValue += dataset[j];

		return mValue / dataset.length;
	}

	static double getStd(double mValue, double[] dataset)
	{
		double sValue = 0.d;

		if (dataset.length == 1)
			return sValue;
		else
		{
			for (int j = 0; j < dataset.length; j++)
				sValue += sqr(mValue - dataset[j]);

			return Math.sqrt(sValue / (dataset.length - 1));
		}
	}

	/* end methods from G.Chinga */

	/* methods from ij.gui.Plot */

	private void build_plot_for_scatter_plot()
	{
		FontMetrics fm			= scatterPlotProcessor.getFontMetrics();
		int fontAscent			= fm.getAscent();
		int MIN_X_GRIDSPACING	= 45;				// minimum distance between grid lines or ticks along x at plot width 0
		int MIN_Y_GRIDSPACING	= 30;				// minimum distance between grid lines or ticks along y at plot height 0
		int LEFT_MARGIN			= 47;
		int maxIntervals		= 12;				// maximum number of intervals between ticks or grid lines
		int tickLength			= 7;				// length of major ticks
		int minorTickLength		= 3;				// length of minor ticks
		int yOfXAxisNumbers		= 305;
		int x1					= xOffset - 2;
		int x2					= xOffset + 2 + 256;
		int y1					= yOffset - 2;
		int y2					= yOffset + 2 + 256;
		int i1, i2, y, digits;
		double  xScale, yScale, xStep, yStep;
		double v;
		String str;	

		scatterPlotProcessor.setColor(255);

		// draw plot legends
		scatterPlotProcessor.drawString(titles[i1Index], xOffset + (256 - scatterPlotProcessor.getStringWidth(titles[i1Index])) / 2, 256 + windowOffset - yOffset + scatterPlotProcessor.getFontMetrics().getHeight());
		scatterPlotProcessor.drawString(titles[i1Index], xOffset + (256 - scatterPlotProcessor.getStringWidth(titles[i1Index])) / 2, 256 + windowOffset - yOffset + scatterPlotProcessor.getFontMetrics().getHeight());
		                     drawYLabel(titles[i2Index], yOffset, yOffset, 256);		

		// draw plot contour
		scatterPlotProcessor.drawRect(xOffset - 1, yOffset - 1, 256 + 3, 256 + 3);		

		// Along X Axis
		xScale = 256 / (max1 - min1);
		xStep  = Math.abs((max1 - min1) * Math.max(1.0 / maxIntervals, (double) MIN_X_GRIDSPACING / 256 + 0.06));	// the smallest allowable step
		xStep  = niceNumber(xStep);
		i1     = (int) Math.ceil (min1 / xStep - 1.e-10);
		i2     = (int) Math.floor(max1 / xStep + 1.e-10);
		digits = getDigits(min1, max1, xStep, 7);
		for (int i = 0; i <= (i2 - i1); i++)
		{
			v = (i + i1) * xStep;
			x = (int) Math.round((v - min1) * xScale) + xOffset - 1;
			// X major ticks
			scatterPlotProcessor.drawLine(x, y1, x, y1 - tickLength);
			scatterPlotProcessor.drawLine(x, y2, x, y2 + tickLength);
			// X numbers
			str = IJ.d2s(v, digits);
			scatterPlotProcessor.drawString(str, x - scatterPlotProcessor.getStringWidth(str) / 2, yOfXAxisNumbers);
		}
		// X minor ticks
		xStep = niceNumber(xStep * 0.19);
		i1 = (int) Math.ceil (min1 / xStep - 1.e-10);
		i2 = (int) Math.floor(max1 / xStep + 1.e-10);
		for (int i = i1; i <= i2; i++)
		{
			v = i * xStep;
			x = (int) Math.round((v - min1) * xScale) + xOffset - 1;
			scatterPlotProcessor.drawLine(x, y1, x, y1 - minorTickLength);
			scatterPlotProcessor.drawLine(x, y2, x, y2 + minorTickLength);
		}

		// Along Y Axis
		yScale = 256 / (max2 - min2);
		yStep = Math.abs((max2 - min2) * Math.max(1.0 / maxIntervals, (double) MIN_Y_GRIDSPACING / 256 + 0.06)); // the smallest allowable step
		yStep = niceNumber(yStep);
		i1 = (int) Math.ceil (min2 / yStep - 1.e-10);
		i2 = (int) Math.floor(max2 / yStep + 1.e-10);
		digits = getDigits(min2, max2, yStep, 5);
		for (int i = i1; i <= i2; i++)
		{
			v = yStep == 0 ? min2 : i * yStep;
			y = yOffset + 256 + 1 - (int) Math.round((v - min2) * yScale);
			// Y major ticks
			scatterPlotProcessor.drawLine(x1, y, x1 - tickLength, y);
			scatterPlotProcessor.drawLine(x2, y, x2 + tickLength, y);
			// Y numbers
			str = IJ.d2s(v, digits);
			scatterPlotProcessor.drawString(str, LEFT_MARGIN - scatterPlotProcessor.getStringWidth(str), y	+ fontAscent * 2 / 3);
		}

		// Y minor ticks
		yStep = niceNumber(yStep * 0.19);
		i1 = (int) Math.ceil(min2 / yStep - 1.e-10);
		i2 = (int) Math.floor(max2 / yStep + 1.e-10);
		for (int i = i1; i <= i2; i++)
		{
			v = i * yStep;
			y = yOffset + 256 + 1 - (int) Math.round((v - min2) * yScale);
			scatterPlotProcessor.drawLine(x1, y, x1 - minorTickLength, y);
			scatterPlotProcessor.drawLine(x2, y, x2 + minorTickLength, y);
		}
	}

	// Number of digits to display the number n with resolution 'resolution';
	// (if n is integer and small enough to display without scientific notation,
	// no decimals are needed, irrespective of 'resolution')
	// Scientific notation is used for more than 'maxDigits' (must be >=3), and indicated
	// by a negative return value
	static int getDigits(double n, double resolution, int maxDigits)
	{
		if (n == Math.round(n) && Math.abs(n) < Math.pow(10, maxDigits - 1) - 1) // integers and not too big
			return 0;
		else
			return getDigits2(n, resolution, maxDigits);
	}

	// Number of digits to display the range between n1 and n2 with resolution 'resolution';
	// Scientific notation is used for more than 'maxDigits' (must be >=3), and indicated
	// by a negative return value
	static int getDigits(double n1, double n2, double resolution, int maxDigits)
	{
		if (n1 == 0 && n2 == 0) return 0;
		return getDigits2(Math.max(Math.abs(n1), Math.abs(n2)), resolution,	maxDigits);
	}

	static int getDigits2(double n, double resolution, int maxDigits)
	{
		int log10ofN = (int) Math.floor(Math.log10(Math.abs(n)) + 1e-7);
		int digits = resolution != 0 ? -(int) Math.floor(Math.log10(Math.abs(resolution)) + 1e-7) : Math.max(0, -log10ofN + maxDigits - 2);
		int sciDigits = -Math.max((log10ofN + digits), 1);
		if      (digits < -2 && log10ofN >= maxDigits)    digits = sciDigits; // scientific notation for large numbers
		else if (digits < 0)                              digits = 0;
		else if (digits > maxDigits - 1 && log10ofN < -2) digits = sciDigits; // scientific notation for small numbers
		return digits;
	}

	// Returns the smallest "nice" number >= v. "Nice" numbers are .. 0.5, 1, 2, 5, 10, 20 ...
	double niceNumber(double v)
	{
		double base = Math.pow(10, Math.floor(Math.log10(v) - 1.e-6));
		if		(v > 5.0000001 * base) return 10 * base;
		else if	(v > 2.0000001 * base) return  5 * base;
		else                           return  2 * base;
	}

	// Vertical text for y axis label
	private void drawYLabel(String yLabel, int xRight, int yFrameTop, int frameHeight)
	{
		if (yLabel.equals(""))
			return;
		FontMetrics fm = scatterPlotProcessor.getFontMetrics();
		int w = scatterPlotProcessor.getStringWidth(yLabel);
		int h = fm.getHeight();
		ImageProcessor label = new ByteProcessor(w, h);
		label.setColor(Color.white);
		label.drawString(yLabel, 0, h);
		label = label.rotateLeft();
		int y2 = yFrameTop + (frameHeight - scatterPlotProcessor.getStringWidth(yLabel)) / 2;
		if (y2 < yFrameTop)
			y2 = yFrameTop;
		int x2 = Math.max(xRight - h, 0);
		scatterPlotProcessor.insert(label, x2, y2);
	}

	/* end methods from ij.gui.Plot */

	public void windowActivated(WindowEvent e)		{}
	
	public void windowOpened(WindowEvent e)			{}

	public void windowClosed(WindowEvent e)			{}

	public void windowClosing(WindowEvent e)
	{
		resultsWindowCreated = false;
	}

	public void windowDeactivated(WindowEvent e)	{}
	
	public void windowDeiconified(WindowEvent e)	{}
	
	public void windowIconified(WindowEvent e)		{}

	public void imageOpened(ImagePlus imp)			{}

	public void imageUpdated(ImagePlus imp)			{}

	public void imageClosed(ImagePlus imp)
	{
		if (imp == this.scatterPlot)
		{
			scatterPlotRoi			.removeRoiListener				(this);
			scatterPlot.getCanvas()	.removeMouseListener			(this);
			scatterPlot.getCanvas()	.removeKeyListener				(this);
			scatterPlotWindow		.removeKeyListener				(this);
		}
		if (imp == this.resultImage)
		{
			resultImageRoi			.removeRoiListener				(this);
			resultImage.getCanvas()	.removeMouseListener			(this);
			resultImage.getCanvas()	.removeMouseMotionListener		(this);
			Prefs.blackBackground	= previousblackBackgroundState;
		}
	}

	public synchronized void roiModified(ImagePlus imp, int id)
	{
		if(id == CREATED && !mouseInsideResultImage && !mouseInsideScatterPlot)
		{
			if (imp == scatterPlot)
			{
				comparison(false, false);
				scatterPlot.draw();
			}
			else if (imp == resultImage)
			{
				rebuild_scatter_plot();
				comparison(false, false);			
			}		
		}	
		else if(imp == scatterPlot)
		{
			if (id == CREATED || id == MODIFIED || id == MOVED || id == COMPLETED)
			{
				scatterPlotModified = true;
				if (bgThread == null)
				{
					bgThread = new Thread(this, "scatterPlot update");
					bgThread.setPriority(Math.max(bgThread.getPriority()-3, Thread.MIN_PRIORITY));
					bgThread.start();
				}
				else
					notify();
			}
//			else if (id == CREATED)
//			{
//				comparison(false, false);
//				scatterPlot.draw();
//			}
		}
		else if(imp == resultImage)
		{
			if (id == CREATED || id == MODIFIED || id == MOVED || id == COMPLETED)
			{
				resultImageModified = true;
				if (bgThread == null)
				{
					bgThread = new Thread(this, "resultImage update");
					bgThread.setPriority(Math.max(bgThread.getPriority()-3, Thread.MIN_PRIORITY));
					bgThread.start();
				}
				else
					notify();
			}
//			else if (id == CREATED)
//			{
//				rebuild_scatter_plot();
//				comparison(false, false);
//			}
		}
	}

	public void mouseClicked(MouseEvent evt)
	{
		clickCount = 0;

		if (evt.getButton() == MouseEvent.BUTTON1 && clickInsideRoi(evt))
		{
			if (evt.getClickCount() == 2)
				doubleClick = true;

			timer = new Timer(multiClickInterval, new ActionListener()
			{
				public void actionPerformed(ActionEvent e)
				{
					if (doubleClick)
					{
						clickCount++;
						if (clickCount == 2)
						{
							comparison(true, true);
							clickCount = 0;
							doubleClick = false;
						}
					}
					else
						comparison(true, false);
				}
			});
			timer.setRepeats(false);
			timer.start();
			if (evt.getID() == MouseEvent.MOUSE_RELEASED)
				timer.stop();
		}
	}

	private boolean clickInsideRoi(MouseEvent evt)
	{
			 if (mouseInsideResultImage)
		{
			if(resultImage.getRoi().contains(resultImage.getCanvas().offScreenX(evt.getX()), resultImage.getCanvas().offScreenY(evt.getY())))
				return true;
			else
				return false;
		}
		else if (mouseInsideScatterPlot)
		{
			if(scatterPlot.getRoi().contains(scatterPlot.getCanvas().offScreenX(evt.getX()), scatterPlot.getCanvas().offScreenY(evt.getY())))
				return true;
			else
				return false;
		}
		return false;
	}

	public void mousePressed(MouseEvent evt) {}

	public void mouseExited(MouseEvent evt)
	{
        icc = (ImageCanvas) evt.getSource();
			 if (icc.getImage() == this.resultImage)
			mouseInsideResultImage = false;
		else if (icc.getImage() == this.scatterPlot)
			mouseInsideScatterPlot = false;
	}

	public void mouseEntered(MouseEvent evt)
	{
        icc = (ImageCanvas) evt.getSource();
			 if (icc.getImage() == this.resultImage)
			mouseInsideResultImage = true;
		else if (icc.getImage() == this.scatterPlot)
			mouseInsideScatterPlot = true;
	}

	public void mouseReleased(MouseEvent evt)
	{
		if (bgThread != null)
			bgThread.interrupt();
		bgThread = null;
		if (scatterPlotModified)
		{
			scatterPlotModified		= false;
			comparison(false, false);
			scatterPlot.draw();
		}
		else if (resultImageModified)
		{
			resultImageModified		= false;
			rebuild_scatter_plot();
			comparison(false, false);
		}
	}

	public void mouseMoved(MouseEvent evt)
	{
		if (mouseInsideResultImage && evt.getModifiers() == ActionEvent.CTRL_MASK)
		{
			scatterPlotRoi	= scatterPlot.getRoi();
			if(scatterPlotRoi == null)
				scatterPlot.setRoi(new Rectangle(50 + xOffset, 50 + yOffset, 150, 150));
			coord			= scatterPlotRoi.getBounds();
			roiWidth		= coord.width;
			roiHeight		= coord.height;
			scatterPlotRoi	.setLocation(Math.round((image1Processor.getPixelValue(resultImage.getCanvas().offScreenX(evt.getX()), resultImage.getCanvas().offScreenY(evt.getY())) * 256 / max1) + xOffset - roiWidth  / 2),
								   256 - Math.round((image2Processor.getPixelValue(resultImage.getCanvas().offScreenX(evt.getX()), resultImage.getCanvas().offScreenY(evt.getY())) * 256 / max2) - yOffset + roiHeight / 2));
			scatterPlot		.killRoi();
			scatterPlot		.restoreRoi();
			comparison(false, false);
/*		
			i3.setRoi(Math.round(image1Processor.getPixelValue(canvasResu.offScreenX(evt.getX()) , canvasResu.offScreenY(evt.getY())) + xOffset - widthR  / 2)
			  , 256 - Math.round(image2Processor.getPixelValue(canvasResu.offScreenX(evt.getX()) , canvasResu.offScreenY(evt.getY())) - yOffset + heightR / 2)
			  , widthR, heightR);
*/
		}
	}

	public void mouseDragged(MouseEvent e) {}

	public void keyPressed(KeyEvent e)
	{
		int keyCode = e.getKeyCode();
//		e.consume();
		if (keyCode == KeyEvent.VK_NUMPAD4 || keyCode == KeyEvent.VK_NUMPAD6)
		{
			long	[] hist1 = image1Statistics.getHistogram();
			double	[] xval1 = new double[image1Statistics.nBins];
			double	[] yval1 = new double[image1Statistics.nBins];
			for (i = 0; i != image1Statistics.nBins; i++)
			{
				xval1[i] = i * (max1 - min1) / image1Statistics.nBins;
				yval1[i] = (double) hist1[i];
			}
			CurveFitter cf1 = new CurveFitter(xval1, yval1);
			cf1.doFit(CurveFitter.GAUSSIAN);
			Fitter.plot(cf1);
			double[] fitParam1 = cf1.getParams();
//			IJ.log(String.valueOf(fitParam1[2]));
//			rt = new ResultsTable();
//			rt.incrementCounter();
//			rt.addValue(titles[i2Index], fitParam1[2]);
//			rt.show(titles[i2Index]);
			StringSelection selection = new StringSelection(String.valueOf(fitParam1[2]));
			Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
			clipboard.setContents(selection, selection);
		}
		else if (keyCode == KeyEvent.VK_NUMPAD2	|| keyCode == KeyEvent.VK_NUMPAD8)
		{
			long	[] hist2 = image2Statistics.getHistogram();
			double	[] xval2 = new double[image2Statistics.nBins];
			double	[] yval2 = new double[image2Statistics.nBins];
			for (i = 0; i != image2Statistics.nBins; i++)
			{
				xval2[i] = i * (max2 - min2) / image2Statistics.nBins;
				yval2[i] = (double) hist2[i];
			}
			CurveFitter cf2 = new CurveFitter(xval2, yval2);
			cf2.doFit(CurveFitter.GAUSSIAN);
			Fitter.plot(cf2);
			double[] fitParam2 = cf2.getParams();
//			IJ.log(String.valueOf(fitParam2[2]));
//			rt = new ResultsTable();
//			rt.incrementCounter();
//			rt.addValue(titles[i1Index], fitParam2[2]);
//			rt.show(titles[i1Index]);
			StringSelection selection = new StringSelection(String.valueOf(fitParam2[2]));
			Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
			clipboard.setContents(selection, selection);
		}
	}

	public void keyReleased(KeyEvent e)
	{
		if (bgThread != null)
			bgThread.interrupt();
		bgThread = null;
		if (scatterPlotModified)
		{
			scatterPlotModified		= false;
			comparison(false, false);
			scatterPlot.draw();
		}
		else if (resultImageModified)
		{
			resultImageModified		= false;
			rebuild_scatter_plot();
			comparison(false, false);
		}
	}

	public void keyTyped(KeyEvent e) {}

	private void defineColors()
	{
		color		= -1;
		colors		= new ColorDefinition[5];
		colors[0]	= new ColorDefinition("red"    , Color.red    , 255,   0,   0);
		colors[1]	= new ColorDefinition("green"  , Color.green  ,   0, 255,   0);
		colors[2]	= new ColorDefinition("blue"   , Color.blue   ,   0,   0, 255);
		colors[3]	= new ColorDefinition("magenta", Color.magenta, 255,   0, 255);
		colors[4]	= new ColorDefinition("cyan"   , Color.cyan   ,   0, 255, 255);
	}

	class ColorDefinition
	{
		public int r, g, b;
		public String name;
		public java.awt.Color color;

		ColorDefinition(String name, java.awt.Color color, int r, int g, int b)
		{
			this.name = name;
			this.color = color;
			this.r = r;
			this.g = g;
			this.b = b;
		}
	}

	public static String getResultsAsString(String separator)
	{
		double value	= getR(lesx, lesy);
		return	( Math.abs(value) < 1e-3
				? String.format		(     "%.7E",	value												)	+ separator
				: Double.toString	(Math.round (	value					 	* 10000000d) / 10000000d)	+ separator)
				+ Double.toString	(Math.round (	getOverlap	(lesx, lesy) 	* 10000000d) / 10000000d)	+ separator
				+ Double.toString	(Math.round (	getContrib	(lesx, lesy) 	* 10000000d) / 10000000d)	+ separator
				+ Double.toString	(Math.round (	getContrib	(lesy, lesx) 	* 10000000d) / 10000000d)	+ separator
				+ Double.toString	(Math.round (	cfParams[1]					*    10000d) /    10000d)	+ separator
				+ Double.toString	(Math.round (	cfParams[0]					*    10000d) /    10000d)	+ separator
				+ Integer.toString	(				counter												)	+ separator
				+ Double.toString	(Math.round (	percentPixels				*     1000d) /     1000d)	+ separator
				+ Integer.toString	(				minI1												)	+ separator
				+ Integer.toString	(				maxI1												)	+ separator
				+ Integer.toString	(				minI2												)	+ separator
				+ Integer.toString	(				maxI2												)	+ separator
				+ Double.toString	(Math.round (	getMean(lesx) * max1 / 255	*      10000d) /  10000d)	+ separator
				+ Double.toString	(Math.round (	getMean(lesy) * max2 / 255	*      10000d) /  10000d)	;
	}
}